{-| Structs are structural data types or values of such a type combining
    features of both tuples and records, or of both sums and unions, depending on
    how the fields are interpreted. If all fields are required to form a value, then
    the struct is a tuple/record hybrid; if exactly one is required, then the 
    struct is a sum/union hybrid.

    Some definitions are in order:

    [Tuple] a structural data type or value aggregating multiple fields indexed by natural numbers.

    [Sum] a structural data type or value selecting exactly one of multiple fields indexed by natural numbers.

    [Record] a structural data type or value aggregating multiple fields indexed by natural numbers.

    [Union] a structural data type or value selecting exactly one of multiple fields indexed by natural numbers.

    Some accounts require records and unions to be nominal types, but this
    consideration is orthogonal to indexing with naturals or names. Nominal versions
    of records, unions and structs may be recovered simply by using some nominalization
    wrapper (such @newtype@ in Haskell).

    There is no reason why a struct must use both positional fields and named fields.
    Either (or both) could just as well be empty. Therefore, tuples, sums, records
    and unions, as defined here, are all special cases of struct.

    Structures can be particularly useful where functions are Curried.
    With aggregating structures, we can easily simulate a mix of positional and keyword
    arguments to such functions.
    There may even be some use for selection structs, such as to specify the type of a function
    which can take one of multiple valid sets of arguments.
-}

module Data.Struct (
    -- * Aggregate Structs
      Struct
    , mkAggregate
    , getIx
    , getKw
    , getEither
    , hasIx
    , hasKw
    , hasEither
    , fieldIx
    , fieldKw
    , fieldEither
    , setIx
    , setKw
    , setEither
    -- * Selection Structs
    , Costruct
    , CostructTemplate
    , mkSelection
    , getFilled
    , whichFilled
    , setFilled
    , emptySelection
    ) where

import Data.List
import Data.Maybe
import Control.Applicative


------ Types ------
{-| Aggregating struct data type.
    Every field of an aggregating struct must be filled.
-}
data Struct k a = Struct [a] [(k, a)]
-- Named fields are given in an association list,
-- since we may wish to index named fields with natural numbers
-- beginning with the first index not used for a positional field.

{-| Selection struct data type.
    There must be exactly one field filled in a selection struct.

    We chose the name Costruct because the relation between 'Struct' and 'Costruct'
    is exactly the duality between product and coproduct (also called sum) types.
-}
-- FIXME horribly inefficient access, storage waste
newtype Costruct k a = Costruct { unCostruct :: Struct k (Maybe a) }
{-| Template from which a costruct may be created.
    Generally, you would define a @'Costruct' MyName MyType@ statically, then transform
    this into a @'CostructTemplate' MyName@ template with 'emptySelection', and use that
    template with 'mkSelection' to create actual @'Costruct' MyName MyValue@ values at
    runtime.
-}
newtype CostructTemplate k = CostructTemplate (Struct k ())


------ Access ------
{-| Look up a positional field. -}
getIx :: Struct k a -> Int -> Maybe a
getIx struct i | hasIx struct i = Just (fieldIx struct i)
               | otherwise      = Nothing

{-| Lookup a named field. -}
getKw :: (Eq k) => Struct k a -> k -> Maybe a
getKw (Struct _ kw) name = lookup name kw

{-| Look up a positional field, but if the index goes past the positional fields,
    look into the named fields.
-}
getEither :: Struct k a -> Int -> Maybe a
getEither struct i | hasEither struct i = Just (fieldEither struct i)
                   | otherwise = Nothing

{-| Check for existence of a positional field -}
hasIx :: Struct k a -> Int -> Bool
hasIx (Struct pos _) i = 0 <= i && i < length pos

{-| Check for existence of a named field -}
hasKw :: (Eq k) => Struct k a -> k -> Bool
hasKw (Struct _ kw) name = name `elem` map fst kw

{-| Check for existence of a positional field, but if the index goes past
    the positional fields, look into the named fields.
-}
hasEither :: Struct k a -> Int -> Bool
hasEither (Struct pos kw) i = 0 <= i && i < length pos + length kw

{-| Look up a positional field. Fails if field does not exist. -}
fieldIx :: Struct k a -> Int -> a
fieldIx (Struct pos _) n = pos !! n

{-| Lookup a named field. Fails if field does not exist. -}
fieldKw :: (Eq k) => Struct k a -> k -> a
fieldKw struct name = fromJust $ getKw struct name

{-| Look up a positional field, but if the index goes past the positional fields,
    look into the named fields. Fails if field does not exist.
-}
fieldEither :: Struct k a -> Int -> a
fieldEither struct@(Struct pos kw) i | hasIx struct i = fieldIx struct i
                                     | otherwise      = snd $ kw !! (i - length pos)


{-| Determine which field is filled in a selection struct. -}
whichFilled :: Costruct k a -> Either Int k
whichFilled (Costruct (Struct pos kw)) = case (Left <$> findPosition) <|> (Right <$> findKeyword) of
        Nothing -> error "no one slot filled"
        Just x -> x
    where
    findPosition = case findIndices isJust pos of
        [x] -> Just x
        _ -> Nothing
    findKeyword = case filter (isJust . snd) kw of
        [(k, _)] -> Just k
        _ -> Nothing

{-| Extract the value of the unique filled field in a selection struct. -}
getFilled :: Costruct k a -> a
getFilled (Costruct (Struct pos kw)) = case findPosition <|> findKeyword of
        Nothing -> error "no one slot filled"
        Just x -> x
    where
    findPosition = case filter isJust pos of
        [x] -> x
        _ -> Nothing
    findKeyword = case filter (isJust . snd) kw of
        [(_, v)] -> v
        _ -> Nothing


------ Modification ------
{-| Modify a positional field of a struct. No change if the field does not exist. -}
setIx :: Struct k a -> Int -> a -> Struct k a
setIx struct@(Struct pos kw) i v | 0 <= i && i < length pos = (Struct (replaceAt i pos v) kw)
                                 | otherwise                = struct

{-| Modify a named field of a struct. No change if the field does not exist. -}
setKw :: Struct k a -> k -> a -> Struct k a
setKw = undefined --STUB

{-| Modify a positional field of a struct, but if the index goes past the
    positional fields, modify in the named fields. No change if the field
    does not exist.
-}
setEither :: Struct k a -> Int -> a -> Struct k a
setEither struct@(Struct pos kw) i v | 0 <= i && i < length pos   = setIx struct i v
                                     | i - length pos < length kw = let name = fst $ kw !! (i - length pos)
                                                                    in Struct pos (replaceAt (i - length pos) kw (name, v))
                                     | otherwise                  = struct

{-| Update the unique filled slot of a selection struct to the passed value. -}
setFilled :: Costruct k a -> a -> Costruct k a
setFilled struct v = Costruct $ case whichFilled struct of
    Left i -> setIx (unCostruct struct) i (Just v)
    Right name -> setKw (unCostruct struct) name (Just v)


------ Creation ------
{-| Form a 'Struct' with all fields filled from lists of positional
    and keyword arguments.

    Provided for symmetry with 'mkSelection'.
-}
mkAggregate :: [a] -> [(k, a)]-> Struct k a
mkAggregate = Struct

{-| For a 'Struct' with exactly one field filled from lists of positional
    and keyword arguments.
-}
mkSelection :: CostructTemplate k -> Either Int k -> a -> Costruct k a
mkSelection struct (Left i) v = Costruct $ setEither (blankTemplate struct) i (Just v)
mkSelection struct (Right name) v = Costruct $ setKw (blankTemplate struct) name (Just v)

{-| Create a 'CostructTemplate' with structure identical to the input. -}
emptySelection :: Struct k a -> CostructTemplate k
emptySelection (Struct pos kw) = CostructTemplate $ Struct (map (const ()) pos) (map (\(name, v) -> (name, ())) kw)




blankTemplate :: CostructTemplate k -> Struct k (Maybe a)
blankTemplate (CostructTemplate (Struct pos kw)) =
    Struct (map (const Nothing) pos) (map (\(name,()) -> (name, Nothing)) kw)

replaceAt i xs x = take (i-1) xs ++ [x] ++ drop i xs