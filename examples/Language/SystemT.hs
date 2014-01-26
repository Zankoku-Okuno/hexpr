module Language.SystemT (run) where

import Data.List (intercalate)
import Data.Maybe
import Data.Either.Combinators
import Data.Text (Text, pack, unpack)
import Data.IORef
import qualified Data.Ref as Ref
import Data.Ref (new, newLifted)
import Text.Parsec ( ParseError, SourcePos, getPosition
                   , try, choice, char, string, letter)
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Data.Hexpr
import Data.Hexpr.Parser
import Data.Hexpr.Desugar
import Data.Gensym
import Data.Environment


run :: FilePath -> IO (Either String ())
run filename = runEitherT $ do
    contents <- liftIO $ readFile filename
    raw <- case parser filename contents of
        Left err -> left (show err)
        Right val -> right val
    cooked <- case desugarExpr raw of
        Left err -> left (show err)
        Right val -> right val
    check <- liftIO $ typecheck cooked
    checked <- case check of
        Left err -> left (show err ++ "\n" ++ show cooked)
        Right val -> right val
    evaled <- liftIO $ eval checked
    liftIO $ do 
        putStr ">>> " >> print raw
        putStr "=>> " >> print cooked
        putStr "==> " >> print checked
        putStr "=== " >> print evaled
        --putStrLn "" >> putStrLn (compile checked)

instance (Ref.C m) => Ref.C (EitherT e m) where new = newLifted


 ------ Parser ------
data Keyword = KwNat | KwArr | KwInc | KwLam | KwRec | KwAnn
    deriving (Eq)
data Atom = K SourcePos Keyword
          | N SourcePos Integer
          | V SourcePos Text
    deriving (Eq)

instance Show Keyword where
    show KwNat = "Nat"
    show KwArr = "->"
    show KwInc = "++"
    show KwLam = "\955"
    show KwRec = "rec"
    show KwAnn = ":"
instance Show Atom where
    show (N _ n) = show n
    show (V _ v) = unpack v
    show (K _ kw) = show kw
instance Show a => Show (Hexpr a) where
    show (Leaf x) = show x
    show (Branch xs) = "(" ++ intercalate " " (map show xs) ++ ")"

lang :: HexprLanguage Hexpr Atom
lang = (emptyLang ()) { _atom = [ choice [ kw ":"      KwAnn
                                         , kw "->"     KwArr
                                         , kw "Nat"    KwNat
                                         , kw "++"     KwInc
                                         , kw "rec"    KwRec
                                         , kw "\955"   KwLam
                                         , kw "lambda" KwLam
                                         ]
                                , liftPos (flip N)         naturalLiteral
                                , liftPos (flip V . pack) (parseIdentifier letter letter)
                                ]
                      , _lineComment = void . try $ string "--"
                      }
    where
    liftPos wrap parse = tokenize $ do
        pos <- getPosition
        x <- wrap <$> parse
        return (x pos)
    kw str res = tokenize $ do
        pos <- getPosition
        x <- try $ string str
        return (K pos res)

parser :: FilePath -> String -> Either ParseError (Hexpr Atom)
parser = runHexprParser lang (parseFile parseBareHexpr)


 ------ Desugar ------
data Type' = Nat' SourcePos | Arr' SourcePos Type' Type'
data Expr' = Var' SourcePos Text
             | Num' SourcePos Integer
             | Inc' SourcePos Expr'
             | Lam' SourcePos (SourcePos, Text) Type' Expr'
             | Rec' SourcePos (SourcePos, Text) Expr' Expr' (SourcePos, Text) Expr'
             | App' Expr' Expr'
             | Ann' SourcePos Expr' Type'

getPos :: Hexpr Atom -> SourcePos
getPos (Leaf (N pos _)) = pos
getPos (Leaf (V pos _)) = pos
getPos (Leaf (K pos _)) = pos
getPos (Branch (x:_)) = getPos x

isKw :: Keyword -> Hexpr Atom -> Bool
isKw kw (Leaf (K _ kw')) = kw == kw'
isKw kw _ = False

instance Show Expr' where
    show (Var' _ x) = unpack x
    show (Num' _ n) = show n
    show (Inc' _ x) = "++ " ++ show x
    show (Lam' _ (_, x) t e) = "(\955 (" ++ unpack x ++ " : " ++ show t ++ ") " ++ show e ++ ")" 
    show (Rec' _ (_, f) n z (_, x) e) = "(rec " ++ unpack f ++ " {z => " ++ show z ++ " | ++(" ++ unpack x ++ ") => " ++ show e ++ "} " ++ show n ++ ")"
    show (App' f x) = "(" ++ show f ++ " " ++ show x ++ ")"
    show (Ann' _ e t) = "(" ++ show e ++ " : " ++ show t ++ ")"
instance Show Type' where
    show (Nat' _) = "Nat"
    show (Arr' _ a r) = "(" ++ show a ++ " -> " ++ show r ++ ")"


type Ds a = Either DesugarError a
data DesugarError = Err SourcePos String

instance Show DesugarError where
    show (Err pos msg) = "Syntax error in " ++ show pos ++ ".\n" ++ msg


desugarType :: Hexpr Atom -> Ds Type'
desugarType = go . rightInfix (isKw KwArr)
    where
    go (Leaf (K pos KwNat)) = Right (Nat' pos)
    go (Branch (Leaf (K pos KwArr):xs)) = case xs of
        [a] -> Left $ Err pos "Missing result type."
        [a, r] -> Arr' pos <$> desugarType a <*> desugarType r
        _ -> error "Something went horribly wrong: more than two arguments to _->_ infix"
    go x = Left $ Err (getPos x) "Expecting type."

desugarExpr :: Hexpr Atom -> Ds Expr'
desugarExpr = go . implicitParens
    where
    implicitParens = addShortParens (isKw KwInc) . addParens isBinder . rightInfix (isKw KwAnn)
        where isBinder x = isKw KwLam x || isKw KwRec x
    go (Leaf atom) = case atom of
        N pos n  -> Right $ Num' pos n
        V pos x  -> Right $ Var' pos x
        K pos kw -> Left $ Err pos ("Unexpected `" ++ show kw ++ "'.")
    go (Branch xs) = case xs of
        [Leaf (K pos KwAnn), e, t] -> desugarAnn pos e t
        Leaf (K pos KwAnn):_ -> error "something has gone horribly wrong: an annotation form doesn't have two arguments"
        Leaf (K pos KwInc):xs -> desugarInc pos xs
        Leaf (K pos KwLam):xs -> desugarLam pos xs
        Leaf (K pos KwRec):xs -> desugarRec pos xs
        xs                    -> desugarApp <$> mapM desugarExpr xs
        where
        desugarAnn :: SourcePos -> Hexpr Atom -> Hexpr Atom -> Ds Expr'
        desugarAnn pos e t = Ann' pos <$> desugarExpr e <*> desugarType t
        desugarInc :: SourcePos -> [Hexpr Atom] -> Ds Expr'
        desugarInc pos xs = case xs of
            [] -> Left $ Err pos "Unexpected `++'."
            [e] -> Inc' pos <$> desugarExpr e
        desugarLam :: SourcePos -> [Hexpr Atom] -> Ds Expr'
        desugarLam pos xs = case xs of
            [] -> Left $ Err pos "Unexpected `\955'."
            [x] -> Left $ Err pos "Missing function body."
            
            (x:e) -> do
                (x, t) <- getVarBind x
                Lam' pos x t <$> desugarExpr (node e)
            where
            getVarBind x@(Leaf _) = Left $ Err (getPos x) "Expected annotated variable."
            getVarBind (Branch xs) = tripBy (isKw KwAnn) missingAnn foundAnn xs
                where
                missingAnn xs = Left $ Err (getPos (head xs)) "Expected annotated variable."
                foundAnn [] ann _ = Left $ Err (getPos ann) "Expected variable."
                foundAnn _ ann [] = Left $ Err (getPos ann) "Expected type after `:'."
                foundAnn [Leaf (V pos x)] _ t = do
                    t' <- desugarType (node t)
                    Right ((pos, x), t')
                foundAnn (x:xs) ann _ = Left $ Err (getPos ann) "Expected variable."
        desugarRec :: SourcePos -> [Hexpr Atom] -> Ds Expr'
        desugarRec pos xs = case xs of
            [recvar, start] -> Left $ Err pos "Missing recurrence base case."
            [recvar, start, zero] -> Left $ Err pos "Missing recurrence relation."
            [recvar, start, zero, elemvar] -> Left $ Err pos "Missing recurrence relation body."
            [recvar, start, zero, elemvar, arr] -> Left $ Err pos "Missing recurrence relation body."
            {- Alright, now `rec` has all the syntactic elements it needs. -}
            (recvar: start: zero: elemvar: arr: body) -> do
                getArr arr
                Rec' pos <$> getVar recvar <*> desugarExpr start
                    <*> desugarExpr zero
                    <*> getVar elemvar
                    <*> desugarExpr (node body)
            where
            getVar (Leaf (V pos f)) = Right (pos, f)
            getVar x = Left $ Err (getPos x) "Expected variable."
            getArr (Leaf (K pos KwArr)) = Right ()
            getArr x = Left $ Err (getPos x) "Expected `->'."
        desugarApp :: [Expr'] -> Expr'
        desugarApp [] = error "something has gone horribly wrong inside the System T compiler: App' []"
        desugarApp [_] = error "something has gone horribly wrong inside the System T compiler: App' [_]"
        desugarApp [f, x] = App' f x
        desugarApp xs = App' (desugarApp $ init xs) (last xs)


 ------ Typecheck ------
type Uniq = Integer
type MetaType = (Uniq, IORef (Maybe Type)) --FIXME make it an STRef

data Type = Nat | Arr Type Type | MetaType MetaType
data Term = Var Text
          | Num Integer
          | Inc Term
          | Rec Text Term Term Text Term
          | Lam Text Term
          | App Term Term
          | Closure (MEnv IO Text Term) Text Term

toType :: Type' -> Type
toType (Nat' _) = Nat
toType (Arr' _ t1 t2) = Arr (toType t1) (toType t2)

instance Show Type where
    show Nat = "Nat"
    show (Arr t1 t2) = show t1 ++  " -> " ++ show t2
    show (MetaType (x, ref)) = "t" ++ show x
instance Show Term where
    show (Var x) = unpack x
    show (Num n) = show n
    show (Inc e) = "++ " ++ show e
    show (Lam x e) = "(\955 " ++ unpack x ++ " " ++ show e ++ ")" 
    show (Rec f n z x e) = "(rec " ++ unpack f ++ " {z => " ++ show z ++ " | ++(" ++ unpack x ++ ") => " ++ show e ++ "} " ++ show n ++ ")"
    show (App f x) = "(" ++ show f ++ " " ++ show x ++ ")"


type Tc a = EnvironmentT Text Type (SymbolGenT Integer (EitherT TypeError IO)) a

data TypeError = UnificationFailure SourcePos Type Type
               | UnboundVariable SourcePos Text
instance Show TypeError where
    show (UnificationFailure pos t1 t2) = "Type error at " ++ show pos ++ "\nExpected: " ++ show t1 ++ "\nFound: " ++ show t2
    show (UnboundVariable pos x) = "Unbound variable `" ++ unpack x ++ "' at " ++ show pos ++ "."

newMetaTy :: Tc Type
newMetaTy = do
    uniq <- lift gensym
    ref <- liftIO $ newIORef Nothing
    return (MetaType (uniq, ref))

failTc :: TypeError -> Tc ()
failTc = lift . lift . left

typecheck :: Expr' -> IO (Either TypeError Term)
typecheck e = runEitherT . runSymbolGenT . evalEnvironmentT [] $ checkTau e =<< newMetaTy


checkTau :: Expr' -> Type -> Tc Term
-- derive that `Γ ⊢ n:Nat`
checkTau (Num' pos n) t = unify pos Nat t >> return (Num n)
-- derive that `Γ,x:t ⊢ x:t`
checkTau (Var' pos x) t = do
    found <- find x
    case found of
        Nothing -> failTc $ UnboundVariable pos x
        Just t' -> unify pos t' t
    return (Var x)
-- derive that `Γ ⊢ ++e : Nat` given
checkTau (Inc' pos e) t = do
    -- that Γ ⊢ e : Nat
    e' <- checkTau e Nat
    unify pos Nat t
    return (Inc e')
-- derive that `Γ ⊢ e1 e2 : t` given
checkTau (App' f x) t = do
    t2 <- newMetaTy
    f' <- checkTau f (Arr t2 t) -- that `Γ ⊢ e1 : t2 -> t`
    x' <- checkTau x t2 -- and that `Γ ⊢ e2 : t2`
    return (App f' x')
-- derive that `Γ ⊢ λ (x : t1) e : t` given
checkTau (Lam' pos (xpos, x) ann e) t = do
    let t1 = toType ann
    -- that `t ~ t1 -> t2`
    t2 <- newMetaTy
    unify pos (Arr t1 t2) t
    -- and that `Γ, x:t1 ⊢ e:t2`
    e' <- localEnv $ do
        bind x t1
        checkTau e t2
    return (Lam x e')
-- derive that `Γ ⊢ rec f { z => e0 | s(x) => e } n : t` given
checkTau (Rec' pos (_, f) n z (_, x) e) t = do
    n' <- checkTau n Nat -- that `Γ ⊢ n : Nat`
    z' <- checkTau z t -- and that `Γ ⊢ e0 : t`
    -- and that `Γ, x:Nat, f:t ⊢ e : t`
    e' <- localEnv $ do
        bind x Nat
        bind f t
        checkTau e t
    return (Rec f n' z' x e')
-- derive that `Γ ⊢ (e : t') : t` given
checkTau (Ann' pos e tpos) t' = do
    let t = toType tpos
    e' <- checkTau e t -- that `Γ ⊢ e : t'`
    unify pos t t' -- and that `t' ~ t`
    return e'

unify :: SourcePos -> Type -> Type -> Tc ()
unify _ Nat Nat = return ()
unify pos (Arr t1 t2) (Arr t1' t2') = do
    unify pos t1 t1'
    unify pos t2 t2'
unify pos (MetaType t) t' = unifyVar pos t t'
unify pos t (MetaType t') = unifyVar pos t' t
unify pos t t' = failTc $ UnificationFailure pos t t'

unifyVar :: SourcePos -> MetaType -> Type -> Tc ()
unifyVar pos tv1@(uniq1, ref1) tv2@(MetaType (uniq2, ref2)) = 
    if uniq1 == uniq2 then return ()
    else do
        m_t1 <- liftIO $ readIORef ref1
        m_t2 <- liftIO $ readIORef ref2
        case (m_t1, m_t2) of
            (Just t1, _) -> unify pos t1 tv2
            (Nothing, Just t2) -> liftIO $ ref1 `writeIORef` (Just t2)
            (Nothing, Nothing) -> liftIO $ ref1 `writeIORef` (Just tv2)
unifyVar pos tv1@(_, ref1) t2 = do
    m_t1 <- liftIO $ readIORef ref1
    case m_t1 of
        Just t1 -> unify pos t1 t2
        Nothing -> liftIO $ ref1 `writeIORef` (Just t2)


 ------ Evaluate ------
type Eval a = EnvironmentIO Text Term a

eval :: Term -> IO Term
eval = evalEnvironmentT [] . reduce

reduce :: Term -> Eval Term
reduce is@(Num n) = return (Num n)
reduce is@(Lam x e) = do
    env <- getActiveEnv
    return (Closure env x e)
reduce is@(Var x) = fromJust <$> find x
reduce is@(Inc e) = do
    (Num n) <- reduce e
    return $ Num (n+1)
reduce is@(App f e2) = do
    (Closure env x e) <- reduce f
    withEnv env $ localEnv $ do
        bind x =<< reduce e2
        reduce e
reduce is@(Rec f n z x e) = do
    n' <- reduce n
    case n' of
        (Num 0) -> reduce z
        (Num i) -> localEnv $ do
            let i' = Num (i-1)
            bind f =<< reduce (Rec f i' z x e)
            bind x i'
            reduce e

