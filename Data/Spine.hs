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
    a) the lists in Nests each have at least one element
    b) there are important semantic differences between one-element lists in a Nest with one element, and those with more elements, and
    c) Unquotes must be nested within a matching Quasiquote.
It would be simple but tedious to lift all of these facts into the type system, so for now, I've settled with partial functions.
-}
module Data.Spine (
      Spine (..)
    , QuasiSpine (..)
    , DeQuasiSpine (..)
    , deQuasiSpine
    , SimplifySpine (..)
    , simplifySpine
    ) where
import Data.List1

{-
TODO
    the nest should really be Nest = One QuasiSpine | Many [QuasiSpine]

    make QuasiSpine a dependent type, dependent on the level of quotation

    nest should probably be List1 (List1 (QuasiSpine a))
-}

data QuasiSpine a = QLeaf      a
                  | QNode      (List1 (QuasiSpine a))
                  | QNest      [[QuasiSpine a]]
                  | Quasiquote (QuasiSpine a)
                  | Unquote    (QuasiSpine a)
    deriving Eq

data Spine a = Leaf a
             | Node (List1 (Spine a))
    deriving Eq


class DeQuasiSpine a where
    quoteForm  :: a
    listForm   :: a
    unnestForm :: a

class (Eq a, DeQuasiSpine a) => SimplifySpine a where
    isCode   :: a -> Bool
    toCode   :: Spine a -> a
    fromCode :: a -> Spine a


deQuasiSpine :: DeQuasiSpine a => QuasiSpine a -> Spine a
deQuasiSpine = trans . impl . normalize
    where
    impl :: (DeQuasiSpine a) => QuasiSpine a -> QuasiSpine a
    impl (Quasiquote (QLeaf x))   = QNode $ Cons1 (QLeaf quoteForm) (Nil1 $ QLeaf x)
    impl (Quasiquote (QNode xs))  = QNode . Cons1 (QLeaf listForm)   $ fmap (impl . Quasiquote) xs
    impl (Quasiquote (QNest xss)) = QNode . Cons1 (QLeaf unnestForm) . toList1 $ map (impl . Quasiquote . wrap) xss
        where
        wrap [x] = x
        wrap xs = QNode . toList1 $ xs
    impl (Quasiquote (Quasiquote x)) = impl . Quasiquote $ impl . Quasiquote $ x
    impl (Quasiquote (Unquote x)) = impl x
    impl x = x
    trans :: QuasiSpine a -> Spine a
    trans (QLeaf x)   = Leaf x
    trans (QNode xs)  = Node $ fmap trans xs
    trans (QNest xss) = Node . toList1 $ concatMap (map trans) xss
    normalize :: QuasiSpine a -> QuasiSpine a
    normalize a = case a of
        QLeaf x        -> a
        QNode (Nil1 x) -> normalize x
        QNode xs       -> QNode $ fmap normalize xs
        QNest [xs]     -> QNode . toList1 $ map normalize xs
        QNest xss      -> QNest $ map (map normalize) xss
        Quasiquote x   -> Quasiquote (normalize x)
        Unquote x      -> Unquote (normalize x)

simplifySpine :: SimplifySpine a => Spine a -> Spine a
simplifySpine x = case x of
    Leaf x  -> Leaf x
    Node (Cons1 q (Nil1 x)) | q == Leaf quoteForm -> Leaf . toCode $ simplifySpine x
    Node (Cons1 l xs)       | l == Leaf listForm  -> 
        let xs' = fmap simplifySpine xs
        in if isCode' `all` fromList1 xs'
          then Leaf . toCode . simplifySpine . Node $ fmap fromCode' xs'
          else Node (Cons1 l xs')
        where
        isCode'   (Leaf x) = isCode x
        fromCode' (Leaf x) = fromCode x
    Node xs -> Node $ fmap simplifySpine xs
