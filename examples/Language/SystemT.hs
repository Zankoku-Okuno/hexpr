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
    liftIO $ do 
        putStr ">>> " >> print raw
        putStr "=>> " >> print cooked
        putStr "==> " >> print checked
    right ()


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
data TypePos = NatPos SourcePos | ArrPos SourcePos TypePos TypePos
data ExprPos = VarPos SourcePos Text
             | NumPos SourcePos Integer
             | IncPos SourcePos ExprPos
             | LamPos SourcePos (SourcePos, Text) TypePos ExprPos
             | RecPos SourcePos (SourcePos, Text) ExprPos ExprPos (SourcePos, Text) ExprPos
             | AppPos ExprPos ExprPos
             | AnnPos SourcePos ExprPos TypePos

instance Show ExprPos where
    show (VarPos _ x) = unpack x
    show (NumPos _ n) = show n
    show (IncPos _ x) = "++ " ++ show x
    show (LamPos _ (_, x) t e) = "(\955 (" ++ unpack x ++ " : " ++ show t ++ ") " ++ show e ++ ")" 
    show (RecPos _ (_, f) n z (_, x) e) = "rec " ++ unpack f ++ " " ++ show n ++ " {z => " ++ show z ++ " | ++(" ++ unpack x ++ ") => " ++ show e ++ "}"
    show (AppPos f x) = "(" ++ show f ++ " " ++ show x ++ ")"
    show (AnnPos _ e t) = "(" ++ show e ++ " : " ++ show t ++ ")"
instance Show TypePos where
    show (NatPos _) = "Nat"
    show (ArrPos _ a r) = "(" ++ show a ++ " -> " ++ show r ++ ")"

type Ds a = Either DesugarError a
data DesugarError = Err SourcePos String

instance Show DesugarError where
    show (Err pos msg) = "Syntax error in " ++ show pos ++ ".\n" ++ msg

getPos :: Hexpr Atom -> SourcePos
getPos (Leaf (N pos _)) = pos
getPos (Leaf (V pos _)) = pos
getPos (Leaf (K pos _)) = pos
getPos (Branch (x:_)) = getPos x

isKw :: Keyword -> Hexpr Atom -> Bool
isKw kw (Leaf (K _ kw')) = kw == kw'
isKw kw _ = False

desugarExpr :: Hexpr Atom -> Ds ExprPos
desugarExpr = go . implicitParens
    where
    implicitParens = addShortParens (isKw KwInc) . addParens isBinder . rightInfix (isKw KwAnn)
        where isBinder x = isKw KwLam x || isKw KwRec x
    go (Leaf atom) = case atom of
        N pos n  -> Right $ NumPos pos n
        V pos x  -> Right $ VarPos pos x
        K pos kw -> Left $ Err pos ("Unexpected `" ++ show kw ++ "'.")
    go (Branch xs) = case xs of
        [Leaf (K pos KwAnn), e, t] -> desugarAnn pos e t
        Leaf (K pos KwAnn):_ -> error "something has gone horribly wrong: an annotation form doesn't have two arguments"
        Leaf (K pos KwInc):xs -> desugarInc pos xs
        Leaf (K pos KwLam):xs -> desugarLam pos xs
        Leaf (K pos KwRec):xs -> desugarRec pos xs
        xs                    -> desugarApp <$> mapM desugarExpr xs
        where
        desugarAnn :: SourcePos -> Hexpr Atom -> Hexpr Atom -> Ds ExprPos
        desugarAnn pos e t = AnnPos pos <$> desugarExpr e <*> desugarType t
        desugarInc :: SourcePos -> [Hexpr Atom] -> Ds ExprPos
        desugarInc pos xs = case xs of
            [] -> Left $ Err pos "Unexpected `++'."
            [e] -> IncPos pos <$> desugarExpr e
        desugarLam :: SourcePos -> [Hexpr Atom] -> Ds ExprPos
        desugarLam pos xs = case xs of
            [] -> Left $ Err pos "Unexpected `\955'."
            [x] -> Left $ Err pos "Missing function body."
            
            (x:e) -> do
                (x, t) <- getVarBind x
                LamPos pos x t <$> desugarExpr (node e)
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
        desugarRec :: SourcePos -> [Hexpr Atom] -> Ds ExprPos
        desugarRec pos xs = case xs of
            [recvar, start] -> Left $ Err pos "Missing recurrence base case."
            [recvar, start, zero] -> Left $ Err pos "Missing recurrence relation."
            [recvar, start, zero, elemvar] -> Left $ Err pos "Missing recurrence relation body."
            [recvar, start, zero, elemvar, arr] -> Left $ Err pos "Missing recurrence relation body."
            {- Alright, now `rec` has all the syntactic elements it needs. -}
            (recvar: start: zero: elemvar: arr: body) -> do
                getArr arr
                RecPos pos <$> getVar recvar <*> desugarExpr start
                    <*> desugarExpr zero
                    <*> getVar elemvar
                    <*> desugarExpr (node body)
            where
            getVar (Leaf (V pos f)) = Right (pos, f)
            getVar x = Left $ Err (getPos x) "Expected variable."
            getArr (Leaf (K pos KwArr)) = Right ()
            getArr x = Left $ Err (getPos x) "Expected `->'."
        desugarApp :: [ExprPos] -> ExprPos
        desugarApp [] = error "something has gone horribly wrong inside the System T compiler: AppPos []"
        desugarApp [_] = error "something has gone horribly wrong inside the System T compiler: AppPos [_]"
        desugarApp [f, x] = AppPos f x
        desugarApp xs = AppPos (desugarApp $ init xs) (last xs)

desugarType :: Hexpr Atom -> Ds TypePos
desugarType = go . rightInfix (isKw KwArr)
    where
    go (Leaf (K pos KwNat)) = Right (NatPos pos)
    go (Branch (Leaf (K pos KwArr):xs)) = case xs of
        [a] -> Left $ Err pos "Missing result type."
        [a, r] -> ArrPos pos <$> desugarType a <*> desugarType r
        _ -> error "Something went horribly wrong: more than two arguments to _->_ infix"
    go x = Left $ Err (getPos x) "Expecting type."


 ------ Typecheck ------
type Uniq = Integer
type TySlot = IORef (Maybe Ty) --FIXME make it an STRef

data Ty = TyNat | TyArr Ty Ty | MetaTy Uniq TySlot
data Expr = Var Text
          | Num Integer
          | Inc Expr
          | Rec Text Expr Expr Text Expr
          | Lam Text Expr
          | App Expr Expr

type Tc a = EnvironmentT Text Ty (SymbolGenT Integer (EitherT TypeError IO)) a
--type Tc a = EitherT TypeError (SymbolGenT Integer (EnvironmentIO Text Ty)) a

data TypeError = UnificationFailure SourcePos Ty Ty
               | UnboundVariable SourcePos Text

instance Show Ty where
    show TyNat = "Nat"
    show (TyArr t1 t2) = show t1 ++  " -> " ++ show t2
    show (MetaTy x ref) = "t" ++ show x
instance Show Expr where
    show (Var x) = unpack x
    show (Num n) = show n
    show (Inc e) = "++ " ++ show e
    show (Lam x e) = "(\955 " ++ unpack x ++ " " ++ show e ++ ")" 
    show (Rec f n z x e) = "rec " ++ unpack f ++ " " ++ show n ++ " {z => " ++ show z ++ " | ++(" ++ unpack x ++ ") => " ++ show e ++ "}"
    show (App f x) = "(" ++ show f ++ " " ++ show x ++ ")"
instance Show TypeError where
    show (UnificationFailure pos t1 t2) = "Type error at " ++ show pos ++ "\nExpected: " ++ show t1 ++ "\nFound: " ++ show t2
    show (UnboundVariable pos x) = "Unbound variable `" ++ unpack x ++ "' at " ++ show pos ++ "."

typecheck :: ExprPos -> IO (Either TypeError Expr)
typecheck e = runEitherT . runSymbolGenT . evalEnvironmentT [] $ checkTau e =<< newMetaTy

checkTau :: ExprPos -> Ty -> Tc Expr
checkTau (NumPos pos n) t' = unify pos TyNat t' >> return (Num n)
checkTau (VarPos pos x) t' = do
    found <- find x
    case found of
        Nothing -> failTc $ UnboundVariable pos x
        Just t -> unify pos t t'
    return (Var x)
checkTau (IncPos pos e) t' = do
    e' <- checkTau e TyNat
    unify pos TyNat t'
    return (Inc e')
checkTau (AppPos f x) t = do
    t2 <- newMetaTy
    f' <- checkTau f (TyArr t2 t)
    x' <- checkTau x t2
    return (App f' x')
checkTau (LamPos pos (xpos, x) t e) t' = do
    (tArg, tRes) <- unifyFun pos t'
    unify xpos tArg (toType t)
    e' <- localEnv $ do
        bind x (toType t)
        checkTau e tRes
    return (Lam x e')
checkTau (RecPos pos (_, f) n z (_, x) e) t = do
    n' <- checkTau n TyNat
    z' <- checkTau z t
    e' <- localEnv $ do
        bind x TyNat
        bind f t
        checkTau e t
    return (Rec f n' z' x e')
checkTau (AnnPos pos e tpos) t' = do
    let t = toType tpos
    e' <- checkTau e t
    unify pos t t'
    return e'

unify :: SourcePos -> Ty -> Ty -> Tc ()
unify _ TyNat TyNat = return ()
unify pos (TyArr t1 t2) (TyArr t1' t2') = do
    unify pos t1 t1'
    unify pos t2 t2'
unify pos t@(MetaTy _ _) t' = unifyVar pos t t'
unify pos t t'@(MetaTy _ ref) = unifyVar pos t' t
unify pos t t' = failTc $ UnificationFailure pos t t'

unifyFun :: SourcePos -> Ty -> Tc (Ty, Ty)
unifyFun pos (TyArr a r) = return (a, r)
unifyFun pos t = do
    argVar <- newMetaTy
    resVar <- newMetaTy
    unify pos t (TyArr argVar resVar)
    return (argVar, resVar)

--FIXME take two types, but the first must be a variable, remove the guard pattern when unifying two tvs in unify
unifyVar :: SourcePos -> Ty -> Ty -> Tc ()
unifyVar pos tv1@(MetaTy uniq1 _) tv2@(MetaTy uniq2 _) | uniq1 == uniq2 = return ()
unifyVar pos tv1@(MetaTy _ ref1) tv2@(MetaTy _ ref2) = do
    m_t1 <- liftIO $ readIORef ref1
    m_t2 <- liftIO $ readIORef ref2
    case (m_t1, m_t2) of
        (Just t1, _) -> unify pos t1 tv2
        (Nothing, Just t2) -> liftIO $ ref1 `writeIORef` (Just t2)
        (Nothing, Nothing) -> liftIO $ ref1 `writeIORef` (Just tv2)
unifyVar pos tv1@(MetaTy _ ref1) t2 = do
    m_t1 <- liftIO $ readIORef ref1
    case m_t1 of
        Just t1 -> unify pos t1 t2
        Nothing -> liftIO $ ref1 `writeIORef` (Just t2)

toType :: TypePos -> Ty
toType (NatPos _) = TyNat
toType (ArrPos _ t1 t2) = TyArr (toType t1) (toType t2)

newMetaTy :: Tc Ty
newMetaTy = do
    uniq <- lift gensym
    ref <- liftIO $ newIORef Nothing
    return (MetaTy uniq ref)

failTc :: TypeError -> Tc ()
failTc = lift . lift . left

instance (Ref.C m) => Ref.C (EitherT e m) where new = newLifted


 ------ Evaluate ------

