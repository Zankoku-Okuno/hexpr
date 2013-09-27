{- Spines are a data structure for representing and storing first-class code objects in a strong-, statically-typed language.

In an untyped language, first-class code may be represented by simple lists, which may then hold both atomic values as well as other lists.
As code objects will need to be manipulated regularly, untyped lists are insuficient in a statically typed language.

Because languages with first-class code benefit greatly from quasiquotation, I also introduce the quasi-spine along with bundled algortihms for transforming quasi-spines into spines.
This transformation requires at least certain special forms to be indicated by some marker in the first position of a spine node.
This convention was chosen because of this tradition in Lisp and ought not to be too limiting for language implementors.
The three special forms in question must
    1) create a code object from a spine,
    2) create a list from any number of values, and
    3) repackage spines analogously to list concatenation, which I call unnesting.

In order to generate the simplest spines of code objects from quasi-spines, I have also developed a simplification algorithm which:
    Turns a sinqle quoted value into a code value
    Turns a list of quoted values into a code value

What may not be obvious in this implementation (because I can't be bothered to use anything more verbose than the builtin list syntax) is that:
    a) (Q)Nodes always have at least one element, 
    b) the lists in Nests each have at least one element, and
    c) Unquotes must be nested within a matching Quasiquote.
It would be simple but tedious to lift all of these facts into the type system, so for now, I've settled with partial functions.
-}

{-# LANGUAGE DeriveFunctor #-}
module Data.Spine (
      Spine (..)
    , QuasiSpine (..)
    , Nested (..)
    , UnQuasiSpine (..)
    , unQuasiSpine
    , SimplifySpine (..)
    , simplifySpine
    ) where

{-
TODO
    if a concat map acts on [code], then reduce it

    make QuasiSpine a dependent type, dependent on the level of quotation

    probably even restrict the lists involved to List1 a = Nil1 a | Cons1 a (List1 a)
-}


data Spine a = Leaf a
             | Node [Spine a]
    deriving Eq


unNestSpine :: ([Nested (QuasiSpine a)] -> [Spine a]) -> QuasiSpine a -> Spine a
unNestSpine f (QLeaf x) = Leaf x
unNestSpine f (QNode xs) = Node $ map (unNestSpine f) xs
unNestSpine f (QNest xss) = Node $ f xss


data QuasiSpine a = QLeaf      a
                  | QNode      [QuasiSpine a]
                  | QNest      [Nested (QuasiSpine a)]
                  | Quasiquote (QuasiSpine a)
                  | Unquote    (QuasiSpine a)
    deriving Eq
data Nested a = One a | Many [a]
    deriving (Eq, Functor)

class UnQuasiSpine a where
    quoteForm  :: a
    listForm   :: a
    unnestForm :: a

unQuasiSpine :: UnQuasiSpine a => QuasiSpine a -> Spine a
unQuasiSpine = trans . impl . normalize
    where
    impl :: (UnQuasiSpine a) => QuasiSpine a -> QuasiSpine a
    impl (Quasiquote (QLeaf x))   = QNode   [QLeaf quoteForm,   QLeaf x]
    impl (Quasiquote (QNode xs))  = QNode . (QLeaf listForm:)   $ map (impl . Quasiquote) xs
    impl (Quasiquote (QNest xss)) = QNode . (QLeaf unnestForm:) $ map (impl . Quasiquote . nest) xss
        where
        nest (One x) = x
        nest (Many xs) = QNode xs
    impl (Quasiquote (Quasiquote x)) = impl . Quasiquote $ impl . Quasiquote $ x
    impl (Quasiquote (Unquote x)) = impl x
    impl x = x
    trans :: QuasiSpine a -> Spine a
    trans = unNestSpine . concatMap $ \xs -> case xs of
            One x -> [trans x]
            Many xs -> map trans xs
    normalize :: QuasiSpine a -> QuasiSpine a
    normalize a = case a of
        QLeaf x         -> a
        QNode [x]       -> normalize x
        QNode xs        -> QNode $ map normalize xs
        QNest [One x]   -> normalize x
        QNest [Many xs] -> QNode $ map normalize xs
        QNest xss       -> QNest $ map (fmap normalize) xss
        Quasiquote x    -> Quasiquote (normalize x)
        Unquote x       -> Unquote (normalize x)


class (Eq a, UnQuasiSpine a) => SimplifySpine a where
    isCode   :: a -> Bool
    toCode   :: Spine a -> a
    fromCode :: a -> Spine a

simplifySpine :: SimplifySpine a => Spine a -> Spine a
simplifySpine x = case x of
    Leaf x  -> Leaf x
    Node [q, x]   | q == Leaf quoteForm -> Leaf . toCode $ simplifySpine x
    Node (l : xs) | l == Leaf listForm  -> let xs' = map simplifySpine xs
                                           in if isCode' `all` xs'
                                             then Leaf . toCode . simplifySpine . Node $ map fromCode' xs'
                                             else Node (l : xs')
        where
        isCode' (Leaf x) = isCode x
        fromCode' (Leaf x) = fromCode x
    Node xs -> Node $ map simplifySpine xs
