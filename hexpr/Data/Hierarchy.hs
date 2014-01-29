{-| The intuition behind a hierarchy is that individuals may form groups, and groups may form groups,
    but no group can have zero individuals under its umbrella.

    There are two main ways hierarchies can form (beyond just being an individual).

    * Two or more groups can merge together (conjoin), forming one group where there 
      were many before.

    * Two or more groups can join up underneath a new group, forming /n+1/ groups where 
      there were /n/ before.

    These are the intuitions behind the two relations that hierarchies support.

-}
module Data.Hierarchy (
      Hierarchy(..)
    , unsafeAdjoins
    , Openable(..)
    , OpenAp
    ) where

{-| A hierarchy is a set, together with an associative operation and a non-associative operation,
    as well as a duality law, which we'll get to after introducing the notation.

    Ideally, I'd call the associative operation @++@ or @\<\>@, but the cool infix operators are
    spoken for already, so I'll have to go with descriptive names.
    Raising items into the hierarchy is done with 'individual'.
    We call the associative operation 'conjoin'
    and the non-associative @adjoins@.
    
    In fact, there are two adjoins, 'adjoinsl' and 'adjoinsr'. Offering only these means we can
    satisfy the invariant that groups recursively have at least one individual. In the discussions
    below, assume that @adjoins@ is of type @[f a] -> [f a] -> f a@, and that when called, at least
    one of the arguments is non-empty.
    
    The names literally mean \"join together\" and \"join to\", which succinctly convey the
    associativity properties of each. Well, \"join to\" might seem non-specific, but consider
    building a house in the wrong order as opposed to joining several cups of water in the wrong
    order. \"Ad-\" and \"con-\" have these meanings, even if the prepositions I've used as
    translation aren't so fine-grained.

    The duality law is:

    @
    a `conjoin` (b `adjoin` c) === (a `adjoin` b) `conjoin` c
    @

    The minimal implementation is 'individual', 'conjoin', and 'adjoinsl'.

    Some hierarchies may be commutative in conjoin and/or adjoin. For example, file systems
    (ignoring links) are hierarchies: adjoin creates new directories (though it is not
    the only way), and 'conjoin' adds files/directories into an existing directory, or creates a
    new two-element directory. Clearly, conjoin is commutative here. For generality, we have
    given default implemetations assuming non-commutativity in both operations.
-}
class Hierarchy h where
    {-| Create a singleton hierarchy. -}
    individual :: a -> h a
    {-| Adjoin exactly two nodes in the same level.
    @
    (a `adjoin` b) `adjoin` c =/= a `adjoin` (b `adjoin` c)
    @
    -}
    adjoin :: h a -> h a -> h a
    adjoin a b = adjoinsl a [b]

    {-| Adjoin many nodes in the same level. The first argument is leftmost. -}
    adjoinsl :: h a -> [h a] -> h a

    {-| Adjoin many nodes in the same level. The first argument is rightmost. -}
    adjoinsr :: [h a] -> h a -> h a
    adjoinsr [] a = a
    adjoinsr (a:as) b = adjoinsl a (as++[b])
    
    {-|
    @
    (a `conjoin` b) `conjoin` c === a `conjoin` (b `conjoin` c)
    @
    -}
    conjoin :: h a -> h a -> h a
    {-| Conjoin one or more hierarchies.

    @
    conjoinsl a [x1, ..., xn] === a `conjoin` x1 `conjoin` ... `conjoin` xn
    @
    -}
    conjoinsl :: h a -> [h a] -> h a
    conjoinsl acc [] = acc
    conjoinsl acc (x:xs) = (acc `conjoin` x) `conjoinsl` xs
    {-| Conjoin one or more hierarchies.

    @
    conjoinsr [x1, ..., xn] a === x1 `conjoin` ... `conjoin` xs `conjoin` a
    @
    -}
    conjoinsr :: [h a] -> h a -> h a
    conjoinsr [] base = base
    conjoinsr (x:xs) base = (x `conjoinsl` xs) `conjoin` base

{-| Package a non-empty list into a hierarchy. Fail on empty input. -}
unsafeAdjoins :: (Hierarchy h) => [h a] -> h a
unsafeAdjoins [] = error "Cannot construct hierarchy of zero elements."
unsafeAdjoins [x] = x
unsafeAdjoins (x:xs) = x `adjoinsl` xs


{-| It is often useful to look at the elements of a node in a 'Hierarchy', perform
    some transformation, then package the result back up as it was originally. Openable
    provides exactly the required functionality. This may be useful more generally as
    well, so we provide it as an independent class that can operate on structures that
    have leaves and/or branches.

    The minimal complete implementation is 'openAp'.
-}
class Openable f where
    {-| Open a node, perform either the leaf or branch transform and close it back up. 
    
    This algorithm should not recursively traverse the structure. Thus, even if the
    structure consists only of leaves, 'openAp' is /not/ a fancy way to say 'fmap'.
    -}
    openAp :: OpenAp f a -> f a -> f a

    {-| Perform a preorder traversal version of 'openAp'. -}
    preorder :: OpenAp f a -> f a -> f a
    preorder f x = (id, fmap $ preorder f) `openAp` (f `openAp` x)

    {-| Perform a postorder traversal version of 'openAp'. -}
    postorder :: OpenAp f a -> f a -> f a
    postorder f x = f `openAp` ((id, fmap $ postorder f) `openAp` x)

{-| Package a transformations for leaves and branches together. -}
type OpenAp f a = (a -> a, [f a] -> [f a])

