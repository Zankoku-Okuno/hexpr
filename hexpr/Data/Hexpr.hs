{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
--TODO some sort of Homoiconic class, which can is required for Functor so that fmap can delve into code objects
-- well, required for functor might be too strong, instead provide a some sort of hmap that can delve, but requires Functor and Homoiconic
{-| Hexprs are a data structure for representing and storing first-class code objects in a
    strongly-, statically-typed language.

    In an untyped language, first-class code may be represented by simple lists, which may then
    hold both atomic values as well as other lists. As code objects will need to be manipulated
    regularly, untyped lists (or @[∀a.a]@, if you prefer) are insufficient in a statically typed
    language. We therefore introduce 'Hexpr's, which is the type of the extended context-free
    grammar family @S ::= @/atom/@ | (SS@/+/@)@.

    By contrast, the grammar of s-exprs is @S ::= @/atom/@ | (SS@/*/@)@, which also has an
    associated type. However, s-exprs are less suitable for mathematical reasoning. Note that
    s-exprs distinguish between @a@ and @(a)@, which is entirely contrary to mathematical notation,
    wherein superfluous parenthesis may be dropped, and often should be for social reasons. While
    I'm at it, I may as well say the grammar of roses is @S ::= @/atom/@ | @/atom/@(S@/*/@)@.

    Because languages with first-class code benefit greatly from quasiquotation, we also introduce
    the 'Quasihexpr', which is isomorphic to 'Hexpr'. We give algorithms for encoding quasihexprs
    into hexprs, see 'UnQuasihexpr' and 'SimplifyHexpr' for more detail. The other direction is
    considered only useful in theoretical work.

    Because we are programming in Haskell, and not Idris, I have decided to leave some invariants
    out of the type system. The documentation of 'Hexpr' and 'Quasihexpr' give these invariants.
    It would make pattern matching too cumbersome to encode these invariants, and some would even
    need extensions. If I were to instead hide the unsafety, it would make pattern matching
    impossible. 
-}
module Data.Hexpr (
    -- * Primary Data Structures
      Hexpr(..)
    , Quasihexpr(..)
    -- * Translation
    , unQuasihexpr
    , simplifyHexpr
    , UnQuasihexpr(..)
    , SimplifyHexpr(..)
    ) where

import Data.List
import Control.Applicative

import Data.Hierarchy


------ Types ------
{-| Whereas a rose contains an element at every level of organization, elements of a hexpr appear
    only in the leaves of the structure. That is, internal nodes (branches) are only responsible
    for grouping consecutive elements and other groups.

    Hexprs further disallow trivial branches, where trivial means containing zero of one children.
    Where there are zero children in a branch, the branch contains no information. Where a branch
    contains only one node, no extra grouping information is provided. As branches are responsible
    for grouping, and grouping alone, it does not make sense to allow branches that contain no
    grouping structure.
    These restrictions on the number of children in a branch are not currently enforced by the
    type system, so several functions on hexprs are properly partial.

    To aid in production-quality language implementation, we also attach a position to each node.
    If position is unneeded, simply specialize to @()@.
-}
data Hexpr p a = Leaf   p a
               | Branch p [Hexpr p a]

{-| A Quasihexpr extends 'Hexpr' with quasiquotation.
    
    In addition to the usual restrictions on hexprs, each 'Unquote' and 'Splice' element must be
    contained within a matching 'Quasiquote' ancestor. Each Quasiquote can match with multiple
    (or zero) Unquote and Splice nodes, just so long as there is no other Quasiquote between.
    Again, this restriction is not enforced by the type system.
-}
data Quasihexpr p a = QLeaf      p a
                    | QBranch    p [Quasihexpr p a]
                    | Quote      p (Quasihexpr p a)
                    | Quasiquote p (Quasihexpr p a)
                    | Unquote    p (Quasihexpr p a)
                    | Splice     p (Quasihexpr p a)


------ Hexpr Transforms ------
{-| Implement this class to allow quasihexprs to be transformed into hexprs by 'unQuasishexpr'.

    The transformation will map 'Quasiquote', 'Unquote' and 'Splice' nodes into special 'Branches'
    whose first element is is a /special form/. That is:

    * the form is a leaf (already enforced by the type system),

    * the semantics of the form should not depend on context,

    * and when translating the hexpr into a richer syntax, the form will disappear in favor of the
      form's siblings being enclosed in some specific type of grammatical node.

    This sort of transformation should make it very easy to detect and handle the resulting
    encoding in appropriately special ways should the need arise.

        
        [Node] create a node from any number of values, and
        
        [Concat] unwrap some input code objects, and construct a single code object from the parts.
-}
class UnQuasihexpr a where
    {-| Create a code literal from its (exactly one) sibling hexpr. -}
    quoteForm  :: a
    {-| A vararg function that creates a single hexpr node from some code values (at least one)
        where the values are obtained by evaluating sibling hexprs.

        That is, given @('nodeForm' \<e_1\> ... \<e_n\>)@ with @n >= 1@, then if each @e_i@
        reduces to a code value @v_i@, then construct a code value equivalent to
        @('quoteForm' (\<v_1\> ... \<v_n\>))@.
    -}
    nodeForm   :: a
    {-| A vararg function that concatenates lists of values into a single node where the lists are
        obtained by evaluating sibling nodes.

        That is, given @('concatForm' \<e_1\> ... \<e_n\>)@ with @n >= 1@, then if each @e_i@
        reduces to a code value @vs_i@, and each @vs_i@ is a list of code values, then construct a
        code value equivalent to @('quoteForm' (\<vs_1\> ++ ... ++ \<vs_n\>))@.  
    -}
    concatForm :: a

{-| Transform a quasihexpr into a hexpr. When the input consists only of 'QLeaf' and 'QBranch'
    nodes, the transformation is trivial. However, 'Quasiquote', 'Unquote' and 'Splice' need to
    be specially encoded. See 'UnQuasihexpr' for more detail on the encoding used. Otherwise, we
    use the following transformations:

    * A quasiquoted leaf is a the leaf wrapped in a 'quoteForm'.

    * For a quasiquoted branch, consecutive non-'Splice' nodes are wrapped in a 'nodeForm', and 
      if there are any 'Splice' nodes in the branch, then all of these results are wrapped in a
      'concatForm'.

    * A quasiquoted unquote/splice node is simply the content of the node.

    Of course, appropriate recursion is also needed, but for that, see the source code. It's
    interesting, but not helpful for understanding the results if you already understand
    quasiquotation.
-}
unQuasihexpr :: UnQuasihexpr a => Quasihexpr p a -> Hexpr p a
unQuasihexpr = error "TODO"
    --trans . impl . normalize
    --where
    --impl :: (UnQuasihexpr a) => Quasihexpr p a -> Quasihexpr p a
    --impl (QBranch p xs)                  = QBranch p (impl <$> xs)
    --impl (Quasiquote q (QLeaf p x))      = QBranch p [QLeaf p quoteForm, QLeaf p x]
    --impl (Quasiquote q (QBranch p xs))   = unquasiquoteBranch xs
    --impl (Quasiquote q (Quasiquote p x)) = pushQuote q . pushQuote q $ x
    --impl (Quasiquote q (Unquote p x))    = impl x
    --impl (Quasiquote q (Splice p x))     = impl x
    --impl x = x
    --trans :: Quasihexpr p a -> Hexpr p a
    --trans (QLeaf x)  = Leaf x
    --trans (QBranch xs) = Branch (map trans xs)
    --trans (Quasiquote _) = error "tried to translate quasiquote"
    --normalize :: Quasihexpr p a -> Quasihexpr p a
    --normalize a = case a of
    --    QLeaf p x      -> a
    --    QBranch p [x]  -> normalize x
    --    QBranch p xs   -> QBranch p (map normalize xs)
    --    Quote p x      -> QBranch p [QLeaf p quoteForm, x]
    --    Quasiquote p x -> Quasiquote p (normalize x)
    --    Unquote p x    -> Unquote p (normalize x)
    --    Splice p x     -> Splice p (normalize x)
    --unquasiquoteBranch xs = case groupBy splitSplices xs of
    --        -- branches always contain at least two nodes
    --        -- @groupBy splitSplices@ never puts splices together in a group
    --        -- therefore, if xss is a singleton, it contains no splices
    --        [xs] -> QBranch (QLeaf nodeForm : map pushQuote xs)
    --        xss  -> QBranch (QLeaf concatForm : map createSpliceList xss)
    --    where
    --        --FIXME REFAC pattern matching from the case into the function def
    --        splitSplices x y = case (x, y) of 
    --            (Splice _, _) -> False
    --            (_, Splice _) -> False
    --            _ -> True
    --        createSpliceList xs = if isSplice xs
    --            then (let [x] = xs in pushQuote x)
    --            else QBranch (QLeaf nodeForm : map pushQuote xs)
    --        isSplice xs = case xs of { [Splice _ _] -> True; _ -> False }
    --pushQuote :: (UnQuasihexpr a) => p -> Quasihexpr p a -> Quasihexpr p a
    --pushQuote p = impl . Quasiquote p

--FIXME I can generalize this to: class ?Homoiconic? f where {toAtom :: f a -> a; fromAtom :: a -> Maybe (f a)}
{-| Implement this class to allow simplification of some hexprs generated by @unQuasiSpine@. See
    'simplifyHexpr' for more details on exactly what transformations are performed.

    In order to simplify a hexpr, we require that any hexpr, no matter how complex, may be turned
    into a single term of the type parameter, @a@. Further, 'toCode' and 'fromCode' are nearly
    inverses of each other.

    @
    'fromCode' . 'toCode' === id
    'toCode' ('fromCode' x) === id      whenever 'isCode' x
    @
-}
class (Eq a, UnQuasihexpr a) => SimplifyHexpr a where
    {-| Whether an atom is a code atom. -}
    isCode   :: a -> Bool
    {-| Create a code atom from a 'Hexpr'. -}
    toCode   :: Hexpr p a -> a
    {-| Extract the 'Hexpr' from a code atom.

        This method need only be total over the refinement type @{x :: a | 'isCode' x}@, not the
        plain type @a@.
    -}
    fromCode :: p -> a -> Hexpr p a

{-| The @unQuasihexpr@ algorithm usually produces hexprs that are more complex than is necessary.
    This function factors @quoteForm@s, @nodeForm@s and @concatForm@s to eliminate redundancy.

    Assuming that 'fromCode' does not fail in the transformations, the particular transforms made
    are as follows. Appropriate recursive searches are made so that no opportunity to simplify is
    lost.

    * @('quoteForm' s)@ ---> @'toCode' s@

    * @('nodeForm' c1 ... cn)@ ---> @('quoteForm' (s1 ... sn))@
        where @si = 'fromCode' ci@

    * @('concatForm' c1 ... cn)@ ---> @('quoteForm' cs)@ 
        where @cs = conjoins ('fromCode' \<$\> [c1, ..., cn])@
        with @conjoins xs = head xs 'conjoinsl' tail xs@

    TODO: The following are unimplemented, but shouldn't matter too much.
    However, ideally the set of Hexprs returned from this function should be
    a proper subset of Hexprs (i.e. a normal form) that is isomorphic to Quasihexpr.
    Probably, once the isomorphism is proven, I'll merge this in with unQuasihexpr

    * @('nodeForm' x1 ... xm) ('quoteForm' xn)@ ---> @('nodeForm' x1 ... xm xn)@

    * @('quoteForm' x0) ('nodeForm' x1 ... xn)@ ---> @('nodeForm' x0 x1 ... xn)@    

    * Any immediate siblings of nodeForm-lead branches are pushed into the nodeForm just so long as
        the parent is not a concatForm-lead branch.
-}
simplifyHexpr :: SimplifyHexpr a => Hexpr p a -> Hexpr p a
simplifyHexpr x = error "TODO"
    --case x of
    --    Leaf p x         -> Leaf p x
    --    Branch p (x:[])  -> simplifyHexpr x
    --    Branch p (q:[x]) | q == Leaf quoteForm -> toCode' $ simplifyHexpr x
    --    Branch p (n:xs)  | n == Leaf nodeForm  ->
    --                        let xs' = simplifyHexpr <$> xs
    --                        in if isCode' `all` xs'
    --                           then toCode' . simplifyHexpr . Branch p $ fromCode' <$> xs'
    --                           else conjoin p n (Branch xs')
    --    Branch p (c:xs)  | c == Leaf concatForm ->
    --                        let xs' = simplifyHexpr <$> xs
    --                        in if isCode' `all` xs'
    --                           then toCode' $ conjoins (fromCode' <$> xs')
    --                           else conjoin p c (Branch xs')
    --    Branch p xs      -> Branch p (simplifyHexpr <$> xs)
    --where
    --isCode' (Leaf p x) = isCode x
    --isCode' _ = False
    --toCode' = Leaf . toCode
    --fromCode' (Leaf p x) = fromCode x

------ Instances ------
instance Eq a => Eq (Hexpr p a) where
    (Leaf _ x) == (Leaf _ y) = x == y
    (Branch _ xs) == (Branch _ ys) = xs == ys
    _ == _ = False
instance Eq a => Eq (Quasihexpr p a) where
    (QLeaf _ x) == (QLeaf _ y) = x == y
    (QBranch _ xs) == (QBranch _ ys) = xs == ys
    (Quote _ x) == (Quote _ y) = x == y
    (Quasiquote _ x) == (Quasiquote _ y) = x == y
    (Unquote _ x) == (Unquote _ y) = x == y
    (Splice _ x) == (Splice _ y) = x == y
    _ == _ = False

--TODO this won't work if there's internal structure in the Leaves
--perhaps if I use `toCode :: Hexpr a -> Hexpr a`, then we needn't worry about internal structure so much`
instance Functor (Hexpr p) where
    fmap f (Leaf p x) = Leaf p (f x)
    fmap f (Branch p xs) = Branch p $ (map . fmap) f xs

instance Functor (Quasihexpr p) where
    fmap f (QLeaf p x) = QLeaf p (f x)
    fmap f (QBranch p xs) = QBranch p $ (map . fmap) f xs
    fmap f (Quote p x) = Quote p (fmap f x)
    fmap f (Quasiquote p x) = Quasiquote p (fmap f x)
    fmap f (Unquote p x) = Unquote p (fmap f x)
    fmap f (Splice p x) = Splice p (fmap f x)

instance Hierarchy Hexpr p where
    getPos (Leaf p _) = p
    getPos (Branch p _) = p

    individual = Leaf
    
    conjoin p (Branch _ as) (Branch _ bs) = Branch p $ as  ++ bs
    conjoin p (Branch _ as) b             = Branch p $ as  ++ [b]
    conjoin p a             (Branch _ bs) = Branch p $ [a] ++ bs
    conjoin p a             b             = Branch p $ [a] ++ [b]

    adjoinsl p x [] = x
    adjoinsl p x xs = Branch p (x:xs)

instance Hierarchy Quasihexpr p where
    getPos (QLeaf p _) = p
    getPos (QBranch p _) = p
    getPos (Quote p _) = p
    getPos (Quasiquote p _) = p
    getPos (Unquote p _) = p
    getPos (Splice p _) = p

    individual = QLeaf
    
    conjoin p (QBranch _ as) (QBranch _ bs) = QBranch p $ as  ++ bs
    conjoin p (QBranch _ as) b              = QBranch p $ as  ++ [b]
    conjoin p a              (QBranch _ bs) = QBranch p $ [a] ++ bs
    conjoin p a              b              = QBranch p $ [a] ++ [b]

    adjoinsl p x [] = x
    adjoinsl p x xs = QBranch p (x:xs)

instance Openable (Hexpr p) where
    openAp (f, _) (Leaf p x) = Leaf p (f x)
    openAp (_, f) (Branch p xs) = adjoins p (f xs)

instance Openable (Quasihexpr p) where
    openAp (f, _) (QLeaf p x) = QLeaf p (f x)
    openAp (_, f) (QBranch p xs) = adjoins p (f xs)
    openAp fs (Quasiquote p x) = Quasiquote p (openAp fs x)
    openAp fs (Unquote p x) = Unquote p (openAp fs x)
    openAp fs (Splice p x) = Splice p (openAp fs x)




