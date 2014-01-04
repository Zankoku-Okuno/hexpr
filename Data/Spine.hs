--TODO some sort of Homoiconic class, which can is required for Functor so that fmap can delve into code objects
-- well, required for functor might be too strong, instead provide a some sort of hmap that can delve, but requires Functor and Homoiconic
{-| Spines are a data structure for representing and storing first-class code objects in a
    strongly-, statically-typed language.

    In an untyped language, first-class code may be represented by simple lists, which may then
    hold both atomic values as well as other lists. As code objects will need to be manipulated
    regularly, untyped lists (or @[∀a.a]@, if you prefer) are insufficient in a statically typed
    language. We therefore introduce 'Spine's, which is the type of the extended context-free
    grammar family @S ::= @/atom/@ | (SS@/+/@)@.

    By contrast, the grammar of s-exprs is @S ::= @/atom/@ | (SS@/*/@)@, which also has an
    associated type. However, s-exprs are less suitable for mathematical reasoning. Note that
    s-exprs distinguish between @a@ and @(a)@, which is entirely contrary to mathematical notation,
    wherein superfluous parenthesis may be dropped, and often should be for social reasons. While
    I'm at it, I may as well say the grammar of roses is @S ::= @/atom/@ | @/atom/@(S@/*/@)@.

    Because languages with first-class code benefit greatly from quasiquotation, we also introduce
    the 'Quasispine', which is isomorphic to 'Spine'. We give algorithms for encoding quasispines
    into spines, see 'UnQuasispine' and 'SimplifySpine' for more detail. The other direction is
    considered only useful in theoretical work.

    Because we are programming in Haskell, and not Idris, I have decided to leave some invariants
    out of the type system. The documentation of 'Spine' and 'Quasispine' give these invariants.
    It would make pattern matching too cumbersome to encode these invariants, and some would even
    need extensions. If I were to instead hide the unsafety, it would make pattern matching
    impossible. 
-}
module Data.Spine (
    -- * Primary Data Structures
      Spine(..)
    , Quasispine(..)
    -- ** General Classes
    , Hierarchy(..)
    -- ** Smart Constructors
    , node
    , quasinode
    -- * Translation
    , unQuasispine
    , simplifySpine
    , UnQuasispine(..)
    , SimplifySpine(..)
    ) where

import Data.List
import Control.Applicative


------ Types ------
{-| Whereas a rose contains an element at every level of organization, elements of a spine appear
    only in the leaves of the structure. That is, internal nodes (branches) are only responsible
    for grouping consecutive elements and other groups.

    Spines further disallow trivial branches, where trivial means containing zero of one children.
    Where there are zero children in a branch, the branch contains no information. Where a branch
    contains only one node, no extra grouping information is provided. As branches are responsible
    for grouping, and grouping alone, it does not make sense to allow branches that contain no
    grouping structure.
    These restrictions on the number of children in a branch are not currently enforced by the
    type system, so several functions on spines are properly partial.
-}
data Spine a = Leaf a
             | Branch [Spine a]
    deriving (Eq)

{-| A Quasispine extends 'Spine' with quasiquotation.
    
    In addition to the usual restrictions on spines, each 'Unquote' and 'Splice' element must be
    contained within a matching 'Quasiquote' ancestor. Each Quasiquote can match with multiple
    (or zero) Unquote and Splice nodes, just so long as there is no other Quasiquote between.
    Again, this restriction is not enforced by the type system.
-}
data Quasispine a = QLeaf      a
                  | QBranch      [Quasispine a]
                  | Quasiquote (Quasispine a)
                  | Unquote    (Quasispine a)
                  | Splice     (Quasispine a)
    deriving (Eq)


------ Data Manipulation ------
{-| Turn a list of 'Spine's into a single one, avoiding trivial branches.
    Of course, the only way to avoid a trivial branch in @node []@ is to reduce to @&#x22A5;@,
    so avoid that.
-}
node :: [Spine a] -> Spine a
node [] = error "spine nodes must have at least one element"
node [x] = x
node xs = Branch xs

{-| As 'node', but for quasispines.
    Obviously, no 'Quasiquote', 'Unquote' or 'Splice' nodes can be returned.
-}
quasinode :: [Quasispine a] -> Quasispine a
quasinode [] = error "quasispine nodes must have at least one element"
quasinode [x] = x
quasinode xs = QBranch xs


------ Spine Transforms ------
{-| Implement this class to allow quasispines to be transformed into spines by @unQuasispine@.

    The transformation will map 'Quasiquote', 'Unquote' and 'Splice' nodes into special 'Branches'
    whose first element is is a /special form/. That is:

    * the form is a leaf (already enforced by the type system),

    * the semantics of the form should not depend on context,

    * and when translating the spine into a richer syntax, the form will disappear in favor of the
      form's siblings being enclosed in some specific type of grammatical node.

    This sort of transformation should make it very easy to detect and handle the resulting
    encoding in appropriately special ways should the need arise.

        
        [Node] create a node from any number of values, and
        
        [Concat] unwrap some input code objects, and construct a single code object from the parts.
-}
class UnQuasispine a where
    {-| Create a code literal from its (exactly one) sibling spine. -}
    quoteForm  :: a
    {-| A vararg function that creates a single spine node from some code values (at least one)
        where the values are obtained by evaluating sibling spines.

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

{-| Transform a quasispine into a spine. When the input consists only of 'QLeaf' and 'QBranch'
    nodes, the transformation is trivial. However, 'Quasiquote', 'Unquote' and 'Splice' need to
    be specially encoded. See 'UnQuasispine' for more detail on the encoding used. Otherwise, we
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
unQuasispine :: UnQuasispine a => Quasispine a -> Spine a
unQuasispine = trans . impl . normalize
    where
    impl :: (UnQuasispine a) => Quasispine a -> Quasispine a
    impl (QBranch xs)                = QBranch (impl <$> xs)
    impl (Quasiquote (QLeaf x))      = QBranch [QLeaf quoteForm, QLeaf x]
    impl (Quasiquote (QBranch xs))   = unquasiquoteBranch xs
    impl (Quasiquote (Quasiquote x)) = pushQuote . pushQuote $ x
    impl (Quasiquote (Unquote x))    = impl x
    impl (Quasiquote (Splice x))     = impl x
    impl x = x
    trans :: Quasispine a -> Spine a
    trans (QLeaf x)  = Leaf x
    trans (QBranch xs) = Branch (map trans xs)
    trans (Quasiquote _) = error "tried to translate quasiquote"
    normalize :: Quasispine a -> Quasispine a
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
    pushQuote :: (UnQuasispine a) => Quasispine a -> Quasispine a
    pushQuote = impl . Quasiquote

--FIXME I can generalize this to: class ?Homoiconic? f where {toAtom :: f a -> a; fromAtom :: a -> Maybe (f a)}
{-| Implement this class to allow simplification of some spines generated by @unQuasiSpine@. See
    'simplifySpine' for more details on exactly what transformations are performed.

    In order to simplify a spine, we require that any spine, no matter how complex, may be turned
    into a single term of the type parameter, @a@. Further, 'toCode' and 'fromCode' are nearly
    inverses of each other.

    @
    'fromCode' . 'toCode' === id
    'toCode' ('fromCode' x) === id      whenever 'isCode' x
    @
-}
class (Eq a, UnQuasispine a) => SimplifySpine a where
    {-| Whether an atom is a code atom. -}
    isCode   :: a -> Bool
    {-| Create a code atom from a 'Spine'. -}
    toCode   :: Spine a -> a
    {-| Extract the 'Spine' from a code atom.

        This method need only be total over the refinement type @{x :: a | 'isCode' x}@, not the
        plain type @a@.
    -}
    fromCode :: a -> Spine a

{-| The @unQuasispine@ algorithm usually produces spines that are more complex than is necessary.
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
    However, ideally the set of Spines returned from this function should be
    a proper subset of Spines (i.e. a normal form) that is isomorphic to Quasispine.
    Probably, once the isomorphism is proven, I'll merge this in with unQuasispine

    * @('nodeForm' x1 ... xm) ('quoteForm' xn)@ ---> @('nodeForm' x1 ... xm xn)@

    * @('quoteForm' x0) ('nodeForm' x1 ... xn)@ ---> @('nodeForm' x0 x1 ... xn)@    

    * Any immediate siblings of nodeForm-lead branches are pushed into the nodeForm just so long as
        the parent is not a concatForm-lead branch.
-}
simplifySpine :: SimplifySpine a => Spine a -> Spine a
simplifySpine x = case x of
        Leaf x         -> Leaf x
        Branch (x:[])  -> simplifySpine x
        Branch (q:[x]) | q == Leaf quoteForm -> toCode' $ simplifySpine x
        Branch (n:xs)  | n == Leaf nodeForm  ->
                        let xs' = simplifySpine <$> xs
                        in if isCode' `all` xs'
                           then toCode' . simplifySpine . Branch $ fromCode' <$> xs'
                           else n `conjoin` Branch xs'
        Branch (c:xs)  | c == Leaf concatForm ->
                        let xs' = simplifySpine <$> xs
                        in if isCode' `all` xs'
                           then toCode' $ conjoins (fromCode' <$> xs')
                           else c `conjoin` Branch xs'
        Branch xs      -> Branch (simplifySpine <$> xs)
    where
    isCode' (Leaf x) = isCode x
    isCode' _ = False
    toCode' = Leaf . toCode
    fromCode' (Leaf x) = fromCode x

------ Instances ------
--TODO this won't work if there's internal structure in the Leaves
--perhaps if I use `toCode :: Spine a -> Spine a`, then we needn't worry about internal structure so much`
instance Functor Spine where
    fmap f (Leaf x) = Leaf (f x)
    fmap f (Branch xs) = Branch $ (map . fmap) f xs

instance Functor Quasispine where
    fmap f (QLeaf x) = QLeaf (f x)
    fmap f (QBranch xs) = QBranch $ (map . fmap) f xs
    fmap f (Quasiquote x) = Quasiquote (fmap f x)
    fmap f (Unquote x) = Unquote (fmap f x)
    fmap f (Splice x) = Splice (fmap f x)

instance Hierarchy Spine where
    individual = Leaf
    
    conjoin a@(Leaf _) b@(Leaf _)   = Branch $ [a] ++ [b]
    conjoin a@(Leaf _) (Branch bs)  = Branch $ [a] ++ bs
    conjoin (Branch as) b@(Leaf _)  = Branch $ as  ++ [b]
    conjoin (Branch as) (Branch bs) = Branch $ as  ++ bs

    adjoin a b = Branch [a, b]

instance Hierarchy Quasispine where
    individual = QLeaf
    
    conjoin a@(QLeaf _) b@(QLeaf _)   = QBranch $ [a] ++ [b]
    conjoin a@(QLeaf _) (QBranch bs)  = QBranch $ [a] ++ bs
    conjoin (QBranch as) b@(QLeaf _)  = QBranch $ as  ++ [b]
    conjoin (QBranch as) (QBranch bs) = QBranch $ as  ++ bs

    adjoin a b = QBranch [a, b]


-- | because I'm willing to be unsafe here, just don't export
conjoins xs = head xs `conjoinsl` tail xs

--FIXME everything below (well, useless comments aside) goes into a new module, `Data.Hierarchy`, possibly in a different package once I have a whole lot of new, very general stuff of my own
--TODO there may also be unordered forms of Hierarchy, in which conjoin and/or adjoin are commutative

--minimal implementation set is individal, conjoin and adjoin
-- a `conjoin` (b `adjoin` c) === (a `adjoin` b) `conjoin` c
-- if it's a pointed, individual = point
-- if it's a monoid, conjoin = mappend (also, it out be ordered)
{-| A hierarchy is a set, together with an associative operation and a non-associative operation,
    as well as a duality law, which we'll get to after introducing the notation.

    Ideally, I'd call the associative operation @++@ or @\<\>@, but the cool infix operators are
    spoken for already, so I'll have to go with descriptive names.
    Raising items into the hierarchy is done with 'individual'.
    We call the associative operation 'conjoin'
    and the non-associative 'adjoin'.
    The names literally mean \"join together\" and \"join to\", which succinctly convey the
    associativity properties of each. Well, \"join to\" might seem non-specific, but consider
    building a house in the wrong order as opposed to joining several cups of water in the wrong
    order. \"Ad-\" and \"con-\" have these meanings, even if the prepositions I've used as
    translation aren't so fine-grained.

    The duality law is:

    @
    a `conjoin` (b `adjoin` c) === (a `adjoin` b) `conjoin` c
    @

    The minimal implementation is 'individual', 'conjoin', 'adjoin'.

    Hierarchies share some properties with other abstract structures, so here are some
    equivalences that must hold, provided the specific structure actually is shared:

    * 'individual' === 'pure' === 'return'

    * 'conjoin' === 'mappend' === '<>' === '<|>'

    Some hierarchies may be commutative in conjoin and/or adjoin. For example, file systems
    (ignoring links) are hierarchies: adjoin creates new directories (though it is not
    the only way), and 'conjoin' adds files/directories into an existing directory, or creates a
    new two-element directory. Clearly, conjoin is commutative here. In 'Spine's, neither operation
    is commutative.
-}
class Hierarchy f where
    {-| Create a singleton hierarchy. -}
    individual :: a -> f a
    {-|
    @
    (a `conjoin` b) `conjoin` c === a `conjoin` (b `conjoin` c)
    @
    -}
    conjoin :: f a -> f a -> f a
    {-|
    @
    (a `adjoin` b) `adjoin` c =/= a `adjoin` (b `adjoin` c)
    @
    -}
    adjoin :: f a -> f a -> f a

    {-| Conjoin one or more hierarchies.

    @
    conjoinsl a [x1, ..., xn] === a `conjoin` x1 `conjoin` ... `conjoin` xn
    @
    -}
    conjoinsl :: f a -> [f a] -> f a
    conjoinsl acc [] = acc
    conjoinsl acc (x:xs) = (acc `conjoin` x) `conjoinsl` xs
    {-| Conjoin one or more hierarchies.

    @
    conjoinsr [x1, ..., xn] a === x1 `conjoin` ... `conjoin` xs `conjoin` a
    @
    -}
    conjoinsr :: [f a] -> f a -> f a
    conjoinsr [] base = base
    conjoinsr (x:xs) base = (x `conjoinsl` xs) `conjoin` base

    --TODO MAYBE adjoinsl/adjoinsr

