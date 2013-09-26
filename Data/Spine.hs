module Data.Spine (
      Spine (..)
    , QuasiSpine (..)
    , DeQuasiSpine (..)
    , deQuasiSpine
    ) where

{-
TODO
    first off, if I'm going to allow type-safe langs to be built on this, we can't use untyped lists to build code values
    that is, where untyped Lisp uses lists (of any value, including other lists, a typed Lisp must use spines
    Or more generally, if a language is represented by a data structure, then code must be built in that data structure

    I'd really like for the Forms to actually be of type (a -> Spine a), so that the representation of forms doesn't matter

    finally, optimize "lists" of "quotes" (spine nodes of spine leafs) into a quoted list
-}

data QuasiSpine a = QLeaf      a
                  | QNode      [QuasiSpine a]
                  | QNest      [[QuasiSpine a]]
                  | Quasiquote (QuasiSpine a)
                  | Unquote    (QuasiSpine a)

data Spine a = Leaf a
             | Node [Spine a]

class DeQuasiSpine a where
    quoteForm  :: a --DEPRECATED
    listForm   :: a --DEPRECATED
    concatForm :: a --DEPRECATED
    voidForm   :: a

    spineLeafForm :: a -- this is basically equivalent to quote
    spineNodeForm :: a -- this is basically equivalent to list
    spineConcatForm :: a -- this will create a spine node from the list of spines provided

deQuasiSpine :: (DeQuasiSpine a) => QuasiSpine a -> Spine a
deQuasiSpine = trans . impl . normalize
    where
    impl :: (DeQuasiSpine a) => QuasiSpine a -> QuasiSpine a
    impl (Quasiquote (QLeaf x)) = QNode [QLeaf quoteForm, QLeaf x]
    impl (Quasiquote (QNode xs)) = QNode . (QLeaf listForm:) $ map (impl . Quasiquote) xs
    impl (Quasiquote (QNest xss)) = QNode . (QLeaf concatForm:) $ map (impl . Quasiquote . wrap) xss
        where
        wrap [x] = x
        wrap xs = QNode xs
    impl (Quasiquote (Quasiquote x)) = impl . Quasiquote $ impl . Quasiquote $ x
    impl (Quasiquote (Unquote x)) = impl x
    impl x = x
    trans :: (DeQuasiSpine a) => QuasiSpine a -> Spine a
    trans (QLeaf x) = Leaf x
    trans (QNode xs) = Node (map trans xs)
    trans (QNest xss) = Node (concatMap (map trans) xss)
    normalize :: (DeQuasiSpine a) => QuasiSpine a -> QuasiSpine a
    normalize (QLeaf x)      = QLeaf x
    normalize (QNode [x])    = normalize x
    normalize (QNode [])     = QLeaf voidForm
    normalize (QNode xs)     = QNode $ map normalize xs
    normalize (QNest [xs])   = QNode $ map normalize xs
    normalize (QNest xss)    = QNest $ map (map normalize) xss
    normalize (Quasiquote x) = Quasiquote (normalize x)
    normalize (Unquote x)    = Unquote (normalize x)
