{-
In this file, we're parsing, typechecking and interpreting Gödel's System T, which is a total programming language over the natrual numbers.
If that doesn't make sense yet, don't worry about it, we'll learn as we go along.

First things first, let's put together the module boilerplate.
We'll need Some basic data types, a little Parsec and some monadic utilities, and of course the Spine tools.
-}

module Language.SystemT (run) where

import Data.List
import Data.Maybe
import Data.Text (Text, pack, unpack)
import Text.Parsec ( ParseError, SourcePos, getPosition
                   , try, choice, char, string, letter)
import Control.Applicative
import Control.Monad
import Data.Spine
import Data.Spine.Parser
import Data.Spine.Desugar


{-
Let's take a look at the plan. We'll parse in a System T expression, desugar it, typecheck it, and finally execute it.
Along the way, we might pick up an error, and we'll have to report that, so we're using an `Either` type. If there was an error, our driver will simply show the message and exit with failure, or else it will exist successfully.
-}
run :: FilePath -> IO (Either String ())
run filename = do
    contents <- readFile filename
    let result = do
        rawSpine <- case parser filename contents of
            Left err -> Left (show err)
            Right val -> Right val
        cookedSpine <- case desugarExpr rawSpine of
            Left err -> Left (show err)
            Right val -> Right val
        normalForm <- return () --STUB
        Right (snd <$> rawSpine, cookedSpine, normalForm)
    case result of
        Right (raw, cooked, val) -> do
            putStr ">> " >> print raw
            putStr "=> " >> print cooked
            return (Right ())
        Left err -> return (Left err)


type Pos a = (SourcePos, a)

{- # Parsing
System T doesn't have any meta programming, so we'll just use Spine.
First, we define our Atom type.
You can see several Kw... constructors, these are simply keywords.
There's also a constructor for natural number literals (N) and variables (V).

We'll go over each of the keywords once we start desugaring.
-}
data Atom = KwNat | KwArr | KwInc | KwLam | KwRec | KwAnn
          | N Integer
          | V Text
    deriving (Eq)

{-
Let's also define some convineinces for later.
-}
instance Show Atom where
    show (N n) = show n
    show (V v) = unpack v
    show KwNat = "Nat"
    show KwArr = "->"
    show KwInc = "++"
    show KwLam = "\955"
    show KwRec = "rec"
    show KwAnn = ":"
instance Show a => Show (Spine a) where
    show (Leaf x) = show x
    show (Branch xs) = "(" ++ intercalate " " (map show xs) ++ ")"

{-
Now that we have our Atom type, we can define a SpineLanguageT.
We won't need to layer this monad, so we can just use SpineLanguage.
We start with (emptyLang ()) because we don't need any state, and then we give how to parse atoms and line comments.
-}
lang :: SpineLanguage Spine (Pos Atom)
lang = (emptyLang ()) { _atom = [ choice [ kw ":"      KwAnn
                                         , kw "->"     KwArr
                                         , kw "Nat"    KwNat
                                         , kw "++"     KwInc
                                         , kw "rec"    KwRec
                                         , kw "\955"   KwLam
                                         , kw "lambda" KwLam
                                         ]
                                , liftPos  N          naturalLiteral
                                , liftPos (V . pack) (parseIdentifier letter letter)
                                ]
                      , _lineComment = void . try $ string "--"
                      }
    where
    liftPos wrap parse = tokenize $ (,) <$> getPosition <*> (wrap <$> parse)
    kw [ch] res = liftPos (const res) (char ch)
    kw str res = liftPos (const res) (try $ string str)
{-
This is a smiple language, so the defaults will work just fine. We also won't bother with block comments.

Note that there's no problem parsing unicode. Here, both "lambda" and "λ" are accepted as KwLam.
-}

{-
Now, I'll just wrap up our language in a simple function so we can use it easily in `run`
For now, we're just parsing one spine at the top level of a file, without the redundant parens.
-}
parser :: FilePath -> String -> Either ParseError (Spine (Pos Atom))
parser = runSpineParser lang (parseFile parseBareSpine)


{- # Desugar
-}
data TypePos = NatPos SourcePos | ArrPos SourcePos TypePos TypePos
data ExprPos = VarPos SourcePos Text
             | NumPos SourcePos Integer
             | IncPos SourcePos ExprPos
             | LamPos SourcePos (SourcePos, Text) TypePos ExprPos
             | RecPos SourcePos (SourcePos, Text) ExprPos ExprPos (SourcePos, Text) ExprPos
             | AppPos [ExprPos]
             | AnnPos SourcePos ExprPos TypePos

instance Show ExprPos where
    show (VarPos _ x) = unpack x
    show (NumPos _ n) = show n
    show (IncPos _ x) = "++ " ++ show x
    show (LamPos _ (_, x) t e) = "(\955 (" ++ unpack x ++ " : " ++ show t ++ ") " ++ show e ++ ")" 
    show (RecPos _ (_, f) n z (_, x) e) = "rec " ++ unpack f ++ " " ++ show n ++ " {z => " ++ show z ++ " | ++(" ++ unpack x ++ ") => " ++ show e ++ "}"
    show (AppPos xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (AnnPos _ e t) = "(" ++ show e ++ " : " ++ show t ++ ")"
instance Show TypePos where
    show (NatPos _) = "Nat"
    show (ArrPos _ a r) = "(" ++ show a ++ " -> " ++ show r ++ ")"


data DesugarError = Err SourcePos String

instance Show DesugarError where
    show (Err pos msg) = "Syntax error in " ++ show pos ++ ".\n" ++ msg

getPos :: Spine (Pos Atom) -> SourcePos
getPos (Leaf (pos,_)) = pos
getPos (Branch (x:_)) = getPos x

isKw :: Atom -> Spine (Pos Atom) -> Bool
isKw kw (Leaf (_, kw')) | kw == kw' = True
isKw kw _ = False

desugarExpr :: Spine (Pos Atom) -> Either DesugarError (ExprPos)
desugarExpr = go . implicitParens
    where
    implicitParens = addShortParens (isKw KwInc) . addParens isBinder . rightInfix (isKw KwAnn)
    isBinder x = isKw KwLam x || isKw KwRec x
    {- The base case is pretty simple: make sure keywords aren't left on their own, translate the rest. -}
    go x@(Leaf (pos, a)) = case a of
        N n -> Right $ NumPos pos n
        V x -> Right $ VarPos pos x
        _   -> Left $ Err (getPos x) ("Unexpected `" ++ show a ++ "'.")
    {-
    For the rest of it, we're taking advantage of special form notation:
    important keywords will have been moded to the front of a branch.
    -}
    go (Branch (x:xs)) | isKw KwAnn x = desugarAnn (getPos x) xs
                       | isKw KwLam x = desugarLam (getPos x) xs
                       | isKw KwRec x = desugarRec (getPos x) xs
                       | isKw KwInc x = desugarInc (getPos x) xs
                       | otherwise = AppPos <$> mapM desugarExpr (x:xs)
        where
        desugarAnn pos [as, bs] = AnnPos pos <$> desugarExpr as <*> desugarType bs
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
                foundAnn [Leaf (pos, V x)] _ t = do
                    t' <- desugarType (node t)
                    Right ((pos, x), t')
                foundAnn (x:xs) ann _ = Left $ Err (getPos ann) "Expected variable."
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
            getVar (Leaf (pos, V f)) = Right (pos, f)
            getVar x = Left $ Err (getPos x) "Expected variable."
            getArr (Leaf (_, KwArr)) = Right ()
            getArr x = Left $ Err (getPos x) "Expected `->'."
        desugarInc pos xs = case xs of
            [] -> Left $ Err pos "Unexpected `++'."
            [e] -> IncPos pos <$> desugarExpr e

desugarType :: Spine (Pos Atom) -> Either DesugarError TypePos
desugarType xs = go $ rightInfix (isKw KwArr) xs
    where
    go ::Spine (Pos Atom) -> Either DesugarError TypePos
    go x@(Leaf (pos, _))  | isKw KwNat x = Right (NatPos pos)
                          | otherwise    = Left $ Err (getPos x) "Expecting type."
    go (Branch [x, a])    | isKw KwArr x = Left $ Err (getPos x) "Missing result type."
    go (Branch [x, a, r]) | isKw KwArr x = ArrPos (getPos x) <$> desugarType a <*> desugarType r
    go (Branch (x:xs))    | isKw KwArr x = Left $ Err (getPos x) "Too many arguments to `->'."
                          | otherwise    = Left $ Err (getPos x) "Expecting type."


 ------ Typecheck ------


 ------ To AST ------
data Type = Nat | Arr Type Type
data Expr = Var Text
          | Num Integer
          | Rec { _init :: Expr, _recur :: Text, _zero :: Expr, _prev :: Text, _body :: Expr }
          | Lam Text Type Expr
          | App Expr Expr


 ------ Evaluate ------

