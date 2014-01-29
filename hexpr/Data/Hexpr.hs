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
    -- ** Smart Constructors
    , node
    , quasinode
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
-}
data Hexpr a = Leaf a
             | Branch [Hexpr a]
    deriving (Eq)

{-| A Quasihexpr extends 'Hexpr' with quasiquotation.
    
    In addition to the usual restrictions on hexprs, each 'Unquote' and 'Splice' element must be
    contained within a matching 'Quasiquote' ancestor. Each Quasiquote can match with multiple
    (or zero) Unquote and Splice nodes, just so long as there is no other Quasiquote between.
    Again, this restriction is not enforced by the type system.
-}
data Quasihexpr a = QLeaf      a
                  | QBranch    [Quasihexpr a]
                  | Quasiquote (Quasihexpr a)
                  | Unquote    (Quasihexpr a)
                  | Splice     (Quasihexpr a)
    deriving (Eq)


------ Data Manipulation ------
{-| Turn a list of 'Hexpr's into a single one, avoiding trivial branches.
    Of course, the only way to avoid a trivial branch in @node []@ is to reduce to @&#x22A5;@,
    so avoid that.
-}
node :: [Hexpr a] -> Hexpr a
node [] = error "hexpr nodes must have at least one element"
node [x] = x
node xs = Branch xs

{-| As 'node', but for quasishexpr.
    Obviously, no 'Quasiquote', 'Unquote' or 'Splice' nodes can be returned.
-}
quasinode :: [Quasihexpr a] -> Quasihexpr a
quasinode [] = error "quasihexpr nodes must have at least one element"
quasinode [x] = x
quasinode xs = QBranch xs


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
unQuasihexpr :: UnQuasihexpr a => Quasihexpr a -> Hexpr a
unQuasihexpr = trans . impl . normalize
    where
    impl :: (UnQuasihexpr a) => Quasihexpr a -> Quasihexpr a
    impl (QBranch xs)                = QBranch (impl <$> xs)
    impl (Quasiquote (QLeaf x))      = QBranch [QLeaf quoteForm, QLeaf x]
    impl (Quasiquote (QBranch xs))   = unquasiquoteBranch xs
    impl (Quasiquote (Quasiquote x)) = pushQuote . pushQuote $ x
    impl (Quasiquote (Unquote x))    = impl x
    impl (Quasiquote (Splice x))     = impl x
    impl x = x
    trans :: Quasihexpr a -> Hexpr a
    trans (QLeaf x)  = Leaf x
    trans (QBranch xs) = Branch (map trans xs)
    trans (Quasiquote _) = error "tried to translate quasiquote"
    normalize :: Quasihexpr a -> Quasihexpr a
    normalize a = case a of
        QLeaf x      -> a
        QBranch [x]  -> normalize x
        QBranch xs   -> QBranch (map normalize xs)
        Quasiquote x -> Quasiquote (normalize x)
        Unquote x    -> Unquote (normalize x)
        Splice x     -> Splice (normalize x)
    unquasiquoteBranch xs = case groupBy splitSplices xs of
            -- branches always contain at least two nodes
            -- @groupBy splitSplices@ never puts splices together in a group
            -- therefore, if xss is a singleton, it contains no splices
            [xs] -> QBranch (QLeaf nodeForm : map pushQuote xs)
            xss  -> QBranch (QLeaf concatForm : map createSpliceList xss)
        where
            --FIXME REFAC pattern matching from the case into the function def
            splitSplices x y = case (x, y) of 
                (Splice _, _) -> False
                (_, Splice _) -> False
                _ -> True
            createSpliceList xs = if isSplice xs
                then (let [x] = xs in pushQuote x)
                else QBranch (QLeaf nodeForm : map pushQuote xs)
            isSplice xs = case xs of { [Splice _] -> True; _ -> False }
    pushQuote :: (UnQuasihexpr a) => Quasihexpr a -> Quasihexpr a
    pushQuote = impl . Quasiquote

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
    toCode   :: Hexpr a -> a
    {-| Extract the 'Hexpr' from a code atom.

        This method need only be total over the refinement type @{x :: a | 'isCode' x}@, not the
        plain type @a@.
    -}
    fromCode :: a -> Hexpr a

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
simplifyHexpr :: SimplifyHexpr a => Hexpr a -> Hexpr a
simplifyHexpr x = case x of
        Leaf x         -> Leaf x
        Branch (x:[])  -> simplifyHexpr x
        Branch (q:[x]) | q == Leaf quoteForm -> toCode' $ simplifyHexpr x
        Branch (n:xs)  | n == Leaf nodeForm  ->
                        let xs' = simplifyHexpr <$> xs
                        in if isCode' `all` xs'
                           then toCode' . simplifyHexpr . Branch $ fromCode' <$> xs'
                           else n `conjoin` Branch xs'
        Branch (c:xs)  | c == Leaf concatForm ->
                        let xs' = simplifyHexpr <$> xs
                        in if isCode' `all` xs'
                           then toCode' $ conjoins (fromCode' <$> xs')
                           else c `conjoin` Branch xs'
        Branch xs      -> Branch (simplifyHexpr <$> xs)
    where
    isCode' (Leaf x) = isCode x
    isCode' _ = False
    toCode' = Leaf . toCode
    fromCode' (Leaf x) = fromCode x

------ Instances ------
--TODO this won't work if there's internal structure in the Leaves
--perhaps if I use `toCode :: Hexpr a -> Hexpr a`, then we needn't worry about internal structure so much`
instance Functor Hexpr where
    fmap f (Leaf x) = Leaf (f x)
    fmap f (Branch xs) = Branch $ (map . fmap) f xs

instance Functor Quasihexpr where
    fmap f (QLeaf x) = QLeaf (f x)
    fmap f (QBranch xs) = QBranch $ (map . fmap) f xs
    fmap f (Quasiquote x) = Quasiquote (fmap f x)
    fmap f (Unquote x) = Unquote (fmap f x)
    fmap f (Splice x) = Splice (fmap f x)

instance Hierarchy Hexpr where
    individual = Leaf
    
    conjoin a@(Leaf _) b@(Leaf _)   = Branch $ [a] ++ [b]
    conjoin a@(Leaf _) (Branch bs)  = Branch $ [a] ++ bs
    conjoin (Branch as) b@(Leaf _)  = Branch $ as  ++ [b]
    conjoin (Branch as) (Branch bs) = Branch $ as  ++ bs

    adjoinsl x [] = x
    adjoinsl x xs = Branch (x:xs)

instance Hierarchy Quasihexpr where
    individual = QLeaf
    
    conjoin (QBranch as) (QBranch bs) = QBranch $ as  ++ bs
    conjoin (QBranch as) b            = QBranch $ as  ++ [b]
    conjoin a            (QBranch bs) = QBranch $ [a] ++ bs
    conjoin a            b            = QBranch $ [a] ++ [b]

    adjoinsl x [] = x
    adjoinsl x xs = QBranch (x:xs)

instance Openable Hexpr where
    openAp (f, _) (Leaf x) = Leaf (f x)
    openAp (_, f) (Branch xs) = node (f xs)

instance Openable Quasihexpr where
    openAp (f, _) (QLeaf x) = QLeaf (f x)
    openAp (_, f) (QBranch xs) = quasinode (f xs)
    openAp fs (Quasiquote x) = Quasiquote (openAp fs x)
    openAp fs (Unquote x) = Unquote (openAp fs x)
    openAp fs (Splice x) = Splice (openAp fs x)

-- | because I'm willing to be unsafe here, just don't export
conjoins xs = head xs `conjoinsl` tail xs

