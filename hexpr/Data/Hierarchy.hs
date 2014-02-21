{-# LANGUAGE MultiParamTypeClasses #-}
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
    , Openable(..)
    , OpenAp
    , adjoinPos, adjoinslPos, adjoinsrPos, adjoinsPos 
    , conjoinPos, conjoinslPos, conjoinsrPos, conjoinsPos 
    ) where

{-| A hierarchy is a set, together with an associative operation and a non-associative operation,
    as well as a duality law, which we'll get to after introducing the notation.

    Although we also provide for source positions, we will omit them for simplicity in this
    description.

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
class Hierarchy h p where
    getPos :: h p a -> p

    individual :: p -> a -> h p a
    
    adjoin :: p -> h p a -> h p a -> h p a
    adjoin pos a b = adjoinsl pos a [b]

    adjoinsl :: p -> h p a -> [h p a] -> h p a

    adjoinsr :: p -> [h p a] -> h p a -> h p a
    adjoinsr pos [] a = a
    adjoinsr pos (a:as) b = adjoinsl pos a (as++[b])
    
    adjoins :: p -> [h p a] -> h p a
    adjoins pos [] = error "Cannot construct hierarchy of zero elements."
    adjoins pos (x:xs) = adjoinsl pos x xs
    
    conjoin :: p -> h p a -> h p a -> h p a
    
    conjoinsl :: p -> h p a -> [h p a] -> h p a
    conjoinsl pos acc [] = acc
    conjoinsl pos acc (x:xs) = conjoinsl pos (conjoin pos acc x) xs
    
    conjoinsr :: p -> [h p a] -> h p a -> h p a
    conjoinsr pos [] base = base
    conjoinsr pos (x:xs) base = conjoin pos (conjoinsl pos x xs) base

    conjoins :: p -> [h p a] -> h p a
    conjoins pos [] = error "Cannot construct hierarchy of zero elements."
    conjoins pos (x:xs) = conjoinsl pos x xs


adjoinPos :: (Hierarchy h p) => h p a -> h p a -> h p a
adjoinPos x y = adjoin (getPos x) x y
adjoinslPos :: (Hierarchy h p) => h p a -> [h p a] -> h p a
adjoinslPos x [] = x
adjoinslPos x ys = adjoinsl (getPos x) x ys
adjoinsrPos :: (Hierarchy h p) => [h p a] -> h p a -> h p a
adjoinsrPos [] x = x
adjoinsrPos xs y = adjoinsr (getPos $ head xs) xs y
adjoinsPos :: (Hierarchy h p) => [h p a] -> h p a
adjoinsPos [] = error "Cannot construct hierarchy of zero elements."
adjoinsPos (x:xs) = adjoinslPos x xs
conjoinPos :: (Hierarchy h p) => h p a -> h p a -> h p a
conjoinPos x y = conjoin (getPos x) x y
conjoinslPos :: (Hierarchy h p) => h p a -> [h p a] -> h p a
conjoinslPos acc [] = acc
conjoinslPos acc (x:xs) = (acc `conjoinPos` x) `conjoinslPos` xs
conjoinsrPos :: (Hierarchy h p) => [h p a] -> h p a -> h p a
conjoinsrPos [] base = base
conjoinsrPos (x:xs) base = (x `conjoinslPos` xs) `conjoinPos` base
conjoinsPos :: (Hierarchy h p) => [h p a] -> h p a
conjoinsPos [] = error "Cannot construct hierarchy of zero elements."
conjoinsPos (x:xs) = conjoinslPos x xs


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

