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
type AtomPos = (SourcePos, Atom)
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
lang :: SpineLanguage Spine AtomPos
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
parser :: FilePath -> String -> Either ParseError (Spine AtomPos)
parser = runSpineParser lang (parseFile parseBareSpine)


{- # Desugar
-}
data TypePos = NatPos SourcePos | ArrPos TypePos TypePos
data ExprPos = VarPos SourcePos Text
             | NumPos SourcePos Integer
             | IncPos SourcePos ExprPos
             | LamPos SourcePos (SourcePos, Text) TypePos ExprPos
             | RecPos SourcePos (SourcePos, Text) ExprPos ExprPos (SourcePos, Text) ExprPos
             | AppPos [ExprPos]
             | AnnPos ExprPos TypePos

instance Show ExprPos where
    show (VarPos _ x) = unpack x
    show (NumPos _ n) = show n
    show (IncPos _ x) = "++" ++ show x
    show (LamPos _ (_, x) t e) = "(\955 (" ++ unpack x ++ " : " ++ show t ++ ") " ++ show e ++ ")" 
    show (RecPos _ (_, f) n z (_, x) e) = "rec " ++ unpack f ++ " " ++ show n ++ " {z => " ++ show z ++ " | ++(" ++ unpack x ++ ") => " ++ show e ++ "}"
    show (AppPos xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (AnnPos e t) = "(" ++ show e ++ " : " ++ show t ++ ")"
instance Show TypePos where
    show (NatPos _) = "Nat"
    show (ArrPos (NatPos _) r) = "Nat -> " ++ show r
    show (ArrPos a r) = "(" ++ show a ++ ") -> " ++ show r


{-
When we were parsing, Parsec already wrapped up its errors nice and tidy.
When desugaring, we don't have this convenience, so let's just quickly define that interface.
-}
data DesugarError = Err SourcePos String

instance Show DesugarError where
    show (Err pos msg) = "Syntax error in " ++ show pos ++ ".\n" ++ msg

{-
It's also nice to have a helper function or two (or five).
The first, getPos, will help us in error reporting.
The other four will help find our keywords and manipulate the spines they appear in.
-}
getPos :: Spine AtomPos -> SourcePos
getPos (Leaf (pos,_)) = pos
getPos (Branch (x:_)) = getPos x

findAtom :: Atom -> [Spine AtomPos] -> Maybe Int
findAtom x xs = match `findIndex` xs
    where
    match (Leaf (_, y)) = x == y
    match _ = False
    
elemAtom :: Atom -> [Spine AtomPos] -> Bool
elemAtom x = isJust . findAtom x

findAbstraction :: [Spine AtomPos] -> Maybe AtomPos
findAbstraction xs = case (KwLam `findAtom` xs, KwRec `findAtom` xs) of
    (Nothing, Nothing) -> Nothing
    (Just lam, Nothing) -> Just . unleaf $ xs !! lam
    (Nothing, Just rec) -> Just . unleaf $ xs !! rec
    (Just lam, Just rec) -> Just $ if lam < rec then unleaf (xs !! lam) else unleaf (xs !! rec)
    where unleaf (Leaf x) = x

splitOnAtom :: Atom -> [Spine AtomPos] -> ([Spine AtomPos], Spine AtomPos, [Spine AtomPos])
splitOnAtom x xs = let (as, bs) = break match xs in (as, head bs, tail bs)
    where
    match :: Spine AtomPos -> Bool
    match (Leaf (_,y)) = x == y
    match _ = False


{-
Now, we put meat on the bones.
There are actually several contexts where we want to desugar.
There are expressions, of course, but we also care about types.
Further, there are some locatinos that must have a particular form.
For example, the parameter to a lambda abstraction must be of the form `variable : type`.
We'll be doing this checking as well.

The big idea is to move keywords to the front of nodes and remove extraneous syntax.
basically, we're getting to a pure Lisp grammar, and we'll deal with special forms later.

Let's begin with expressions, as they're the biggest part of this.
-}

desugarExpr :: Spine AtomPos -> Either DesugarError (ExprPos)
{- The base case is pretty simple: make sure keywords aren't left on their own, translate the rest. -}
desugarExpr x@(Leaf (pos, a)) = case a of
    N n -> Right (NumPos pos n)
    V x -> Right (VarPos pos x)
    _ -> Left $ Err (getPos x) ("Unexpected `" ++ show a ++ "'.")
{-
Now then, we want to detect keywords in order from least- to most-tightly binding.
Let's say abstractions (lambda and rec) bind least tightly, then annotations, then incrementing.
We also shouldn't find `Nat` or `->` in an expression (they're types), so we check for that error while we're here.
Of course, if we don't find any keywords in a branch, that's no big deal, just recurse down.
-}
desugarExpr (Branch xs) | isJust (findAbstraction xs) = desugarBinder
                        | KwAnn `elemAtom` xs = desugarAnn
                        | KwInc `elemAtom` xs = desugarInc
                        | KwNat `elemAtom` xs = let (_,x,_) = splitOnAtom KwNat xs
                                                in Left $ Err (getPos x) ("Unexpected `" ++ show x ++ "'.")
                        | KwArr `elemAtom` xs = let (_,x,_) = splitOnAtom KwArr xs
                                                in Left $ Err (getPos x) ("Unexpected `" ++ show x ++ "'.")
                        | otherwise = AppPos <$> mapM desugarExpr xs
    where
    desugarBinder = do
        let (Just kw) = findAbstraction xs 
            (as, x, bs) = snd kw `splitOnAtom` xs
        when (null bs) $ Left $ Err (getPos x) ("Unexpected `" ++ show kw ++ "'.")
        func <- desugarBind kw (node bs)
        if null as
            then Right func
            else do
                as' <- mapM desugarExpr as
                Right $ AppPos (as' ++ [func])
    desugarAnn = do
        let (as, x, bs) = KwAnn `splitOnAtom` xs
        as' <- desugarExpr (node as)
        bs' <- desugarType (node bs)
        Right $ AnnPos as' bs'
    desugarInc = do
            let (as, x, rest) = KwInc `splitOnAtom` xs
            (x', bs) <- goIn [IncPos (getPos x)] rest
            as' <- mapM desugarExpr as
            --Left $ Err (getPos x) (show $ (as', x', bs'))
            if null bs
                then if null as'
                    then Right x'
                    else Right $ AppPos (as' ++ [x'])
                else do
                    bs' <- desugarExpr (node bs)
                    Right $ AppPos (as' ++ [x', bs'])
        where
        goIn as [Leaf (pos, KwInc)] = Left $ Err pos "Expected argument after `++'."
        goIn as (Leaf (pos, KwInc):bs) = goIn (IncPos pos:as) bs
        goIn as (b:bs) = do
            b' <- desugarExpr b
            return (goOut b' as, bs)
        goOut acc [] = acc
        goOut acc (inc:xs) = goOut (inc acc) xs

desugarType :: Spine AtomPos -> Either DesugarError TypePos
desugarType (Leaf (pos, KwNat)) = return (NatPos pos)
desugarType xs = Left $ Err (getPos xs) "STUB desugarType"

desugarBind :: AtomPos -> Spine AtomPos -> Either DesugarError ExprPos
{- Both kinds of abstraction need arguments. -}
desugarBind (pos, KwLam) x@(Leaf _) = Left $ Err pos "Expected variable binding."
desugarBind (pos, KwRec) x@(Leaf _) = Left $ Err pos "Expected recursion binding."
{-
Now then, a lambda abstraction is fairly straightforward.
System T includes the simply typed lambda calculus, and this is all that lambda abstraction is.
Specifically, the syntax is `λ (<variable> : <type>) <body>`.
If you aren't familiar with lambda calculus either, we'll see what this means below.
-}
desugarBind (pos, KwLam) (Branch (var:body)) = do
        (x, t) <- getVarBind var
        body' <- desugarExpr (node body)
        Right $ LamPos pos x t body'
    where
    getVarBind x@(Leaf _) = Left $ Err (getPos x) "Expected variable binding."
    getVarBind (Branch xs) = do
        when (not . isJust $ KwAnn `findAtom` xs) $ Left $ Err (getPos (head xs)) "Expected type annotation on variable binding."
        let (x, _, t) = KwAnn `splitOnAtom` xs
        x' <- case x of
            [Leaf (pos,(V x))] -> Right (pos, x)
            _ -> Left $ Err (getPos (head x)) "Expected variable."
        t' <- desugarType (node t)
        return (x', t')
{-
Recursion is a slightly trickier abstraction, but is essentially a recurrence relation.
Since we haven't introduced definitions, we'll need to introduce a variable so the body has a handle to the recurrence.
The syntax we're using is `rec <rec-var> <start> <zero> <elem-var> -> <body>`.

First things first, plenty of error checking.
-}
desugarBind (pos, KwRec) (Branch [recvar, start]) = Left $ Err pos "Missing recurrence base case."
desugarBind (pos, KwRec) (Branch [recvar, start, zero]) = Left $ Err pos "Missing recurrence relation."
desugarBind (pos, KwRec) (Branch [recvar, start, zero, elemvar]) = Left $ Err pos "Missing recurrence relation body."
desugarBind (pos, KwRec) (Branch [recvar, start, zero, elemvar, arr]) = Left $ Err pos "Missing recurrence relation body."
{- Alright, now `rec` has what it needs. -}
desugarBind (pos, KwRec) (Branch (recvar:start:zero:elemvar:arr:body)) = do
    recvar' <- case recvar of
        Leaf (pos, V f) -> Right (pos, f)
        _ -> Left $ Err (getPos recvar) "Expected variable."
    start' <- desugarExpr start
    zero' <- desugarExpr zero
    elemvar' <- case elemvar of
        Leaf (pos, V x) -> Right (pos, x)
        _ -> Left $ Err (getPos elemvar) "Expected variable."
    case arr of
        Leaf (_, KwArr) -> return ()
        _ -> Left $ Err (getPos elemvar) "Expected `->'."
    body' <- desugarExpr (node body)
    Right $ RecPos pos recvar' start' zero' elemvar' body'


 ------ Typecheck ------


 ------ To AST ------
data Type = Nat | Arr Type Type
data Expr = Var Text
          | Num Integer
          | Rec { _init :: Expr, _recur :: Text, _zero :: Expr, _prev :: Text, _body :: Expr }
          | Lam Text Type Expr
          | App Expr Expr


 ------ Evaluate ------

