{- Spines are a data structure for representing and storing first-class code objects in a strongly-, statically-typed language.

In an untyped language, first-class code may be represented by simple lists, which may then hold both atomic values as well as other lists.
As code objects will need to be manipulated regularly, untyped lists are insuficient in a statically typed language.

Because languages with first-class code benefit greatly from quasiquotation, I also introduce the quasi-spine along with algortihms for transforming quasi-spines into spines.
This transformation requires at least certain special forms to be indicated by some marker in the first position of a spine node.
This convention was chosen because of this tradition in Lisp and ought not to be too limiting for language implementors.
The three special forms in question must
    1) create a code object from a spine,
    2) create a list from any number of values, and
    3) repackage spines analogously to list concatenation, which I call unnesting.

In order to generate the simplest spines of code objects from quasi-spines, I have also developed a simplification algorithm which:
    Turns [quote form, value] spine into a code value
    Turns [list form, code values...] into a code value
    Turns [unnest form, code values...] into a code value

What may not be obvious in this implementation is that Unquotes must be nested within a matching Quasiquote.
It would be simple but tedious to lift this fact into the type system, so for now, I've settled with partial functions.
-}

module Data.Spine (
      Spine (..)
    , QuasiSpine (..)
    , UnQuasiSpine (..)
    , unQuasiSpine
    , SimplifySpine (..)
    , simplifySpine
    ) where
import Data.List

{-
TODO
    make QuasiSpine a dependent type, dependent on the level of quotation

    make my own functor instances, so I don't need compiler support
-}

data Spine a = Leaf a
             | Node [Spine a]
    deriving Eq

data QuasiSpine a = QLeaf      a
                  | QNode      [QuasiSpine a]
                  | Quasiquote (QuasiSpine a)
                  | Unquote    (QuasiSpine a)
                  | Splice     (QuasiSpine a)
    deriving Eq

class UnQuasiSpine a where
    quoteForm  :: a
    listForm   :: a
    unnestForm :: a

unQuasiSpine :: UnQuasiSpine a => QuasiSpine a -> Spine a
unQuasiSpine = trans . impl . normalize
    where
    impl :: (UnQuasiSpine a) => QuasiSpine a -> QuasiSpine a
    impl (Quasiquote (QLeaf x))      = QNode [QLeaf quoteForm, QLeaf x]
    impl (Quasiquote (QNode xs))     = unquasiquoteNode xs
    impl (Quasiquote (Quasiquote x)) = pushQuote . pushQuote $ x
    impl (Quasiquote (Unquote x))    = impl x
    impl (Quasiquote (Splice x))     = impl x
    impl x = x
    trans :: QuasiSpine a -> Spine a
    trans (QLeaf x)  = Leaf x
    trans (QNode xs) = Node (map trans xs)
    normalize :: QuasiSpine a -> QuasiSpine a
    normalize a = case a of
        QLeaf x       -> a
        QNode [x]     -> normalize x
        QNode xs      -> QNode (map normalize xs)
        Quasiquote x  -> Quasiquote (normalize x)
        Unquote x     -> Unquote (normalize x)
        Splice x      -> Splice (normalize x)
    unquasiquoteNode xs = case groupBy splitSplices xs of
            [xs] | isSplice xs -> error "unquote splicing really unimplemented"
                 | otherwise   -> QNode (QLeaf listForm : map pushQuote xs)
            xss -> QNode (QLeaf unnestForm : map createSpliceList xss)
        where
            splitSplices x y = case (x, y) of 
                (Splice _, _) -> False
                (_, Splice _) -> False
                _ -> True
            createSpliceList xs = if isSplice xs
                then (let [x] = xs in pushQuote x)
                else QNode (QLeaf listForm : map pushQuote xs)
            isSplice xs = case xs of { [Splice _] -> True; _ -> False }
    pushQuote :: (UnQuasiSpine a) => QuasiSpine a -> QuasiSpine a
    pushQuote = impl . Quasiquote

class (Eq a, UnQuasiSpine a) => SimplifySpine a where
    isCode   :: a -> Bool
    toCode   :: Spine a -> a
    fromCode :: a -> Spine a

simplifySpine :: SimplifySpine a => Spine a -> Spine a
simplifySpine x = case x of
        Leaf x       -> Leaf x
        Node (x:[])  -> simplifySpine x
        Node (q:[x]) | q == Leaf quoteForm -> toCode' $ simplifySpine x
        Node (l:xs)  | l == Leaf listForm  ->
                        let xs' = map simplifySpine xs
                        in if isCode' `all` xs'
                          then toCode' . simplifySpine . Node $ map fromCode' xs'
                          else Node (l:xs')
        Node (c:xs)  | c == Leaf unnestForm ->
                        let xs' = map simplifySpine xs
                        in if isCode' `all` xs'
                          then toCode' . Node $ concatMap (unnest . fromCode') xs'
                          else Node (c:xs')
        Node xs   -> Node (map simplifySpine xs)
    where
    isCode' (Leaf x) = isCode x
    isCode' _ = False
    toCode' = Leaf . toCode
    fromCode' (Leaf x) = fromCode x
    unnest (Leaf x) = [Leaf x]
    unnest (Node xs) = xs

