{-| Finite types are well-known in theory. For those who aren't theorists, there are two kinds of
    finite type: finite products and finite sums (also called finite coproducts). 

    Finite products are a generalization of tuples and records. Where tuples are indexed by
    integer and records ar eindexed by name, finite products can use any index set. Finite sums
    are a generalization of discriminated unions (also called variants) so that, again, they are
    indexed by any set.

    Finite products and sums are useful generally for organizing data, but can be particularly
    useful where functinos are curried. A finite product using @Either Int String@ (or similar)
    as an index set, we can easily simulate a mix of positional and keyword arguments to such
    functions. With finite sums, we can specify the type of a function which can take one of
    multiple valid sets of arguments.
-}
module Data.FiniteType (
      Product
    , mkProduct
    , getProd
    , setProd
    , hasProd
    , Sum
    , mkSum
    , getSum
    , setSum
    , hasSum
    , SumTemplate
    , mkSumTemplate
    ) where

import Data.List
import Data.Maybe
import Control.Applicative


------ Types ------
{-| Types where every field in the index set is filled with a value. -}
data Product i a = Product [(i, a)]

{-| Types where exactly one feild in the index set is filled with a value. -}
data Sum i a = Sum i a (SumTemplate i)

{-| Template from which a finite sum may be created.
    
    Generally, you would define a @'Product' MyIxSet MyType@ in your language's statics,
    then transform this into a @'SumTemplate' MyIxSet@ template with 'mkSumTemplate', and use
    that template with 'mkSum' to create actual @'Sum' MyIxSet MyValue@ values in your
    interpreter.
-}
data SumTemplate i = SumTemplate [i]


------ Creation ------
{-| Form a 'Product' with all fields filled from an association list.
    Error if the keys are not distinct.
-}
mkProduct :: (Eq i) => [(i, a)] -> Product i a
mkProduct xs = let ixSet = fst <$> xs
               in if ixSet == nub ixSet
                    then Product xs
                    else error "Finite Product: index set not distinct"

{-| Form a 'Sum' filling the passed index with the passed value. -}
mkSum :: (Eq i) => SumTemplate i -> i -> a -> Sum i a
mkSum t i v = Sum i v t



{-| Create a 'SumTemplate' with index set identical to the input. -}
mkSumTemplate :: Product i a -> SumTemplate i
mkSumTemplate (Product xs) = SumTemplate (fst <$> xs)
-- don't have to check for distinct, because that's guaranteed by Product invariant


------ Access ------
{-| Look up a field of a finite product. Error if the field does not exist. -}
getProd :: (Eq i) => Product i a -> i -> a
getProd (Product xs) i = fromJust $ i `lookup` xs

{-| Extract the value of the unique filled field in a finite sum. -}
getSum :: Sum i a -> a
getSum (Sum i a t) = a

{-| Check for existence of a field in a finite product. -}
hasProd :: (Eq i) => Product i a -> i -> Bool
hasProd (Product xs) i = i `elem` (fst <$> xs)

{-| Determine which field is filled in a finite sum. -}
hasSum :: Sum i a -> i
hasSum (Sum i x t) = i


------ Modification ------
{-| Modify a field of a finite product. Error if the field does not exist. -}
setProd :: (Eq i) => Product i a -> i -> a -> Product i a
setProd (Product xs) i v = Product (go xs [])
    where
    go [] xs' = error "Finite Product: field not in index set"
    go (x:xs) xs' | i == fst x = reverse xs' ++ (i, v):xs
                  | otherwise = go xs (x:xs')

{-| Modify a field of a finite sum. Error if the field does not exist. -}
setSum :: (Eq i) => Sum i a -> i -> a -> Sum i a
setSum (Sum _ _ t@(SumTemplate is)) i v = if i `elem` is
                            then Sum i v t
                            else error "Finite Sum: field not in index set"

