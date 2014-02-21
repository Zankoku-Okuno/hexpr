module Language.Desugar (
    -- * List Splitting
      tripBy
    , revTripBy
    , SplitFunction
    -- * Implicit Parenthesis
    , addParens
    , addShortParens
    -- * Simple Infixes
    , leftInfix
    , rightInfix
    , nonInfix
    ) where

import Data.List
import Data.Hierarchy
import Data.Hexpr


{-| Transform a list based on the presence and location of an element.

    The first function of the pair is applied when no element was found.
    Its parameter is the original list.

    The second of the pair is applied with an element is found.
    Its parameters are (in order) the preceding elements, the found element, and the
    following elements.
-}
type SplitFunction a b = ([a] -> b, [a] -> a -> [a] -> b)

{-| Split a list at the first element that matched the predicate.
    If the element was not found, apply the 'SplitFunction'.
-}
tripBy :: (a -> Bool) -> SplitFunction a b -> [a] -> b
tripBy p (onNo, onYes) xs = case break p xs of
    (before, []) -> onNo xs
    (before, x:after) -> onYes before x after

{-| As 'tripBy', but search from the end.
-}
revTripBy :: (a -> Bool) -> SplitFunction a b -> [a] -> b
revTripBy p (onNo, onYes) xs = case break p (reverse xs) of
    (rBefore, []) -> onNo xs
    (rAfter, rBefore) -> onYes (reverse rBefore) (last rAfter) (reverse $ init rAfter)

{-| Create a group around a found subnode and all following nodes.
    If no node was found, then there is no change.

    E.g
@
    (a b lambda x y z) ===> (a b (lambda x y z))
@
-}
addParens :: (Openable (h p), Hierarchy h p) => (h p a -> Bool) -> h p a -> h p a
addParens p = openAp (id, tripBy p (id, onYes))
    where
    onYes before x after = before ++ [x `adjoinslPos` after]

{-| Add parenthesis around a found subnode and at most one following node.
    Associates to the right.
    If no node was found, then there is no change.

    E.g.
@
    (++ ++ x) ===> (++(++(x)))
@
-}
addShortParens :: (Openable (h p), Hierarchy h p) => (h p a -> Bool) -> h p a -> h p a
addShortParens p = openAp (id, tripBy p (id, onYes))
    where
    onYes before x [] = before++[x]
    onYes before x after' = case span p after' of
        ([], []) -> [x]
        (cont, []) -> before++[deepen (last cont) (reverse (x:init cont))]
        (cont, next:after) -> before ++ [deepen next (reverse (x:cont))] ++ after
        where
        deepen acc [] = acc
        deepen acc (x:xs) = deepen (x `adjoinPos` acc) xs


{-| Desugar a left-associative infix. If there are no elements to either
    side of the infix, there is no change.

    E.g.
@
    (a b + c d + e f) ===> (+ (+ (a b) (c d)) (e f))
@
-}
leftInfix :: (Openable (h p), Hierarchy h p) => (h p a -> Bool) -> h p a -> h p a
leftInfix p = openAp (id, revTripBy p (id, onYes))
    where
    onYes [] x after = x:after
    onYes before x [] = before++[x]
    onYes before x after = [x, leftInfix p (adjoinsPos before), adjoinsPos after]

{-| Desugar a right-associative infix. If there are no elements to either
    side of the infix, there is no change.

    E.g.
@
    (a b ** c d ** e f) ===> (** (a b) (** (c d) (e f)))
@
-}
rightInfix :: (Openable (h p), Hierarchy h p) => (h p a -> Bool) -> h p a -> h p a
rightInfix p = openAp (id, tripBy p (id, onYes))
    where
    onYes [] x after = x:after
    onYes before x [] = before++[x]
    onYes before x after = [x, adjoinsPos before, rightInfix p (adjoinsPos after)]

{-| Desugar a non-associative infix. If there are no elements to either
    side of the infix, or if multiple matching elements are present,
    there is no change.

    E.g.
@
    (a b < c d) ===> (< (a b) (c d))
    (a b < c d < e f) ===> (a b < c d < e f)
@
-}
nonInfix :: (Openable (h p), Hierarchy h p) => (h p a -> Bool) -> h p a -> h p a
nonInfix p = openAp (id, tripBy p (id, onYes))
    where
    onYes [] x after = x:after
    onYes before x [] = before++[x]
    onYes before x after = if tripBy p (const True, \_ _ _ -> False) after
                            then before ++ [x] ++ after
                            else [x, adjoinsPos before, adjoinsPos after]

