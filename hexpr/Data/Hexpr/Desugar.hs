module Data.Hexpr.Desugar (
      tripBy
    , tripByEnd
    , addParens
    , addShortParens
    , leftInfix
    , rightInfix
    ) where

import Data.List
import Data.Hexpr

tripBy :: (a -> Bool) -> ([a] -> b) -> ([a] -> a -> [a] -> b) -> [a] -> b
tripBy p onNo onYes xs = case break p xs of
    (before, []) -> onNo xs
    (before, x:after) -> onYes before x after

tripByEnd :: (a -> Bool) -> ([a] -> b) -> ([a] -> a -> [a] -> b) -> [a] -> b
tripByEnd p onNo onYes xs = case break p (reverse xs) of
    (rBefore, []) -> onNo xs
    (rAfter, rBefore) -> onYes (reverse rBefore) (last rAfter) (reverse $ init rAfter)

--FIXME generalize
addParens :: (Hexpr a -> Bool) -> Hexpr a -> Hexpr a
addParens p x@(Leaf _)  = x
addParens p (Branch xs) = tripBy p node onYes xs
    where
    onYes before x after = node (before ++ [node (x:after)])

--FIXME generalize
addShortParens :: (Hexpr a -> Bool) -> Hexpr a -> Hexpr a
addShortParens p x@(Leaf _)  = x
addShortParens p (Branch xs) = tripBy p node onYes xs
    where
    onYes before x [] = node (before ++ [x])
    onYes before x after' = case span p after' of
        ([], []) -> x
        (cont, []) -> node $ before ++ [deepen (last cont) (reverse (x:init cont))]
        (cont, next:after) -> node (before ++ [deepen next (reverse (x:cont))] ++ after)
        where
        deepen acc [] = acc
        deepen acc (x:xs) = deepen (node [x, acc]) xs

--FIXME generalize
leftInfix :: (Hexpr a -> Bool) -> Hexpr a -> Hexpr a
leftInfix p x@(Leaf _)  = x
leftInfix p (Branch xs) = tripByEnd p node onYes xs
    where
    onYes [] x after = node (x:after)
    onYes before x [] = node (before ++ [x])
    onYes before x after = node [x, leftInfix p (node before), node after]

--FIXME generalize
rightInfix :: (Hexpr a -> Bool) -> Hexpr a -> Hexpr a
rightInfix p x@(Leaf _)  = x
rightInfix p (Branch xs) = tripBy p node onYes xs
    where
    onYes [] x after = node (x:after)
    onYes before x [] = node (before ++ [x])
    onYes before x after = node [x, node before, rightInfix p (node after)]

