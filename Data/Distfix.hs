{-| We present an algorithm for de-sugaring distributed affixes (distfixes) in a rose-like data
    structure. Distfixes are also known as "mixfixes", but I chose "dist-" because the part of the
    affix are distributed in-order through the root, rather than mixed in (possibly out-of-order)
    with the root. Now then, let's actually describe a distfix in detail:
    
    By rose-like data structure, we mean any type `a` such that if an element of `a` can be
    `unwrap`ped into a list of `a`, then we can perform rewrites according to our distfix
    algorithm, and `rewrap` the result. If that element cannot be `unwrap`ped, then it will be
    left alone during rewriting. Of course, this library was meant to operate on Spines and
    QuasiSpines, but it could just as well work on a plain list or rose, as well as anything else
    you're willing to mangle into shape.

    A distributed affix consists of a number of alternating 'keywords' and 'slots'. While keywords
    should match exactly one leaf node, slots can consume multple nodes (leaves or brances) during
    a detection. If we denote slots by underscores and keywords by some reasonable programming
    language identifier (w/o underscores), then some representative distfix examples might be
    `_+_`, `_?_:_`, `_!` `if_then_else_`, and `while_do_end`.

    Using the algorithm requires categorizing the input distfixes in several dimentions: topology,
    associativity, priority, and precedence. Only precedence need by specified by the user (it is
    extrinsic to any distfix), the rest are either specified in or calculated from the
    construction of the distfix at hand. We discuss these properties below:

    TODO documentation

    <topology closed, open, half-open>
    <associativity>
    <priority>
    <precedence>
    <when we unwrap, we assume the wrapping was parens, so that's all done first>

    <rewriting merely adds parenthesis, never removes, and the only motion is removing the keywords and replacing them with a single leaf at the stqart of the rewritten node>

    <separate structure and detect classes mean we don't need FlexibleInstances extension>

    <not sure how prioroty/detection will work if the same keyword appears twice in the same distfix, prolly best to avoid for now>
    <precedence table stored in ascending order>
-}

module Data.Distfix (
      Distfix(..)
    , Topology(..)
    , DistfixStructure(..)
    , DistfixDetect(..)
    , DistfixTable
    , runDistfix
    , DistfixError(..)
    ) where

import Data.Ord
import Data.List
import Data.Maybe
import Data.Either
import Control.Monad


------ Types ------
class DistfixStructure a where
    nodeMatch :: a -> a -> Bool
    unwrap :: a -> Maybe [a]
    rewrap :: [a] -> a
class DistfixDetect a where
    match :: a -> a -> Bool


data Distfix a = Distfix a Topology [a]
data Topology = Closed | HalfOpenRight | HalfOpenLeft | OpenRight | OpenLeft | OpenNon
type DistfixTable a = [[Distfix a]]

type Match a = (Distfix a, [a], [[a]], [a])
data MatchResult a = NoMatch
                   | OneMatch (Match a)
                   | Ambiguous [Match a]
data DistfixError a = AmbiguousErr [Match a]
                    | LeftoverErr [a]
type DistfixResult a = Either (DistfixError a) a


------ Instances ------
instance Show a => Show (DistfixError a) where
    show (AmbiguousErr matches) = headText ++ concatMap (const "\n\thi") matches --map (("\n\t"++) . show . rewrite id) matches
        where headText = "Ambiguous distfix parse. Could have been one of:"
    show (LeftoverErr [k]) = "Leftover keyword: " ++ show k
    show (LeftoverErr ks) = "Leftover keywords:" ++ concatMap ((' ':) . show) ks

------ Main Algorithm ------
runDistfix :: DistfixStructure a => DistfixTable a -> a -> DistfixResult a
runDistfix table x = case unwrap x of
    Nothing -> return x
    Just xs -> mapM (runDistfix table) xs >>= impl table
    where
    impl [] xs = findLeftovers allKeywords xs
    impl table'@(row:rows) xs = case resolve row xs of
        NoMatch -> impl rows xs
        OneMatch op -> rewrite (impl table') op
        Ambiguous ops -> Left $ AmbiguousErr ops
    allKeywords = nubBy nodeMatch . (concatMap . concatMap) (\(Distfix _ _ ks) -> ks) $ table

rewrite :: DistfixStructure a => ([a] -> DistfixResult a) -> Match a -> DistfixResult a
rewrite recurse (Distfix distfix _ _, [], inside, []) = do
    inside' <- mapM recurse inside
    return . rewrap $ distfix : inside'
rewrite recurse (Distfix distfix _ _, [], inside, after) = do
    inside' <- mapM recurse inside
    after'  <- recurse after
    return . rewrap $ distfix : inside' ++ [after']
rewrite recurse (Distfix distfix _ _, before, inside, []) = do
    before' <- recurse before
    inside' <- mapM recurse inside
    return . rewrap $ distfix : before' : inside'
rewrite recurse (Distfix distfix _ _, before, inside, after) = do
    before' <- recurse before
    inside' <- mapM recurse inside
    after'  <- recurse after
    return . rewrap $ distfix : before' : inside' ++ [after']


------ Selection ------
-- | Given a bunch of distfixes (at the same precedence level), try to find an unambiguous distfix parse within a list
resolve :: DistfixStructure a => [Distfix a] -> [a] -> MatchResult a
resolve ops xs = resolve detectAll []
    where
    detectAll = catMaybes $ map (detect xs) ops
    resolve [] eqSet = case eqSet of
        []  -> NoMatch
        [x] -> OneMatch x
        xs  -> Ambiguous xs
    resolve (x:xs) eqSet = if      is Lower  then resolve xs eqSet
                           else if is Higher then resolve xs [x]
                           else                   resolve xs (x:eqSet)
        where is = (`elem` map (decidePriority x) eqSet)

{-| Given two matches `a` and `b`, determine when `a` should be matched in relation to `b`.
    If `a` should be handled first, then evaluate to has `Higher`. If later, `Lower`, and if there's no precedence rule, then `None`.
    
    The rules are these:
        If both distfixes have the same associativity,
            The one with the "most significant" keyword "earliest" has priority:
                Left-associative: most significant = first, earliest = leftmost
                Right-associative: most significant = last, earliest = rightmost
            If its a still a tie, then the one with the most keywords has priority
        If both distfixes are closed, then they must be non-overlapping, or one must contain the other
            It doesn't really matter which we do first if they don't overlap, we've chosen leftmost for now
            If one nests within the other, the outer has priority
            If they overlap exactly, then the one with the most keywords has priority
        Other pairs of matches have no priority relation
-}
decidePriority :: Match a -> Match a -> Priority
--TODO TESTME I'm sure I mucked up the logic somewhere in here
decidePriority a@(Distfix _ topA ksA, bA, iA, aA) b@(Distfix _ topB ksB, bB, iB, aB) = case (topA, topB) of
    (OpenLeft,      OpenLeft)      -> decideLeft
    (OpenLeft,      HalfOpenLeft)  -> decideLeft
    (HalfOpenLeft,  OpenLeft)      -> decideLeft
    (HalfOpenLeft,  HalfOpenLeft)  -> decideLeft
    (OpenRight,     OpenRight)     -> decideRight
    (OpenRight,     HalfOpenRight) -> decideRight
    (HalfOpenRight, OpenRight)     -> decideRight
    (HalfOpenRight, HalfOpenRight) -> decideRight
    (Closed,        Closed)        -> decideClosed
    (Closed,        _)             -> Higher
    (_,             Closed)        -> Lower
    _                              -> None
    where
    decideRight = leftmost `joinPriority` mostKeywords
        where leftmost = fromOrd . negOrd $ comparing leftmostKeyword a b
    decideLeft = rightmost `joinPriority` mostKeywords
        where rightmost = fromOrd $ comparing rightmostKeyword a b
    decideClosed = leftmostNoOverlap `joinPriority` outermost `joinPriority` (if exactOverlap then mostKeywords else None)
        where
        leftmostNoOverlap = if aR < bL then Higher else if bR < aL then Lower else None
        outermost = case (compare aL bL, compare aR bR) of
            (LT, GT) -> Higher -- `a b b a`
            (GT, LT) -> Lower  -- `b a a b`
            (LT, EQ) -> Higher -- `a b ab`
            (GT, EQ) -> Lower  -- `b a ab`
            (EQ, LT) -> Lower  -- `ab a b`
            (EQ, GT) -> Higher -- `ab b a`
            _ -> None
        exactOverlap = aL == bL && aR == bR
        aL = leftmostKeyword a
        aR = rightmostKeyword a
        bL = leftmostKeyword b
        bR = rightmostKeyword b
    mostKeywords = fromOrd $ comparing impl a b
        where impl (Distfix _ _ ks, _, _, _) = length ks
    -- index of leftmost keyword in the original node
    leftmostKeyword (Distfix _ OpenRight _, _, inside, _) = length (head inside)
    leftmostKeyword (Distfix _ HalfOpenRight _, before, _, _) = length before
    leftmostKeyword (Distfix _ Closed _, before, _, _) = length before
    -- index of rightmost keyword in the original node
    rightmostKeyword (Distfix _ OpenLeft _, _, inside, _) = sum (map length $ init inside) + (length (init inside) - 1)
    rightmostKeyword (Distfix _ HalfOpenLeft _, _, inside, _) = sum (map length inside) + (length inside - 1)
    rightmostKeyword (Distfix _ Closed _, before, inside, _) = length before + sum (map length inside) + length inside


------ Detection ------
findLeftovers :: DistfixStructure a => [a] -> [a] -> DistfixResult a
findLeftovers ks xs = case filter (\x -> any (nodeMatch x) ks) xs of
    [] -> return . rewrap $ xs
    errs -> Left $ LeftoverErr errs

detect :: DistfixStructure a => [a] -> Distfix a -> Maybe (Match a)
detect xs fix@(Distfix _ topology ks) = do
    when (length ks == 0) $ error "distfixes must have at least one keyword"
    (before, inside, after) <- case topology of
        Closed -> do
            when (length ks < 2) $ error "closed distfixes must have at least two keywords"
            (as, ds) <- findKey    (head ks)          xs
            (cs, bs) <- revFindKey (last ks)          ds
            res      <- detectBody (init . tail $ ks) cs
            return (as, res, bs)
        HalfOpenRight -> error "unimplemented" --STUB
        HalfOpenLeft -> error "unimplemented" --STUB
        OpenRight -> do
            (as, bs) <- findKey (head ks) xs
            res <- detectBody (tail ks) bs
            return ([], as:res, [])
        OpenLeft -> do
            (as, bs) <- revFindKey (last ks) xs
            res <- revDetectBody (init ks) as
            return ([], res++[bs], [])
        OpenNon -> error "unimplemented" --STUB
    if any null inside
        then Nothing
        else return (fix, before, inside, after)

detectBody :: DistfixStructure a => [a] -> [a] -> Maybe [[a]]
detectBody [] xs = Just [xs]
detectBody (k:ks) xs = do
    (as, bs) <- findKey k xs
    liftM (as:) (detectBody ks bs)
revDetectBody :: DistfixStructure a => [a] -> [a] -> Maybe [[a]]
revDetectBody ks xs = liftM (map reverse) $ impl (reverse ks) (reverse xs)
    where
    impl [] xs = Just [xs]
    impl (k:ks) xs = do
        (bs, as) <- revFindKey k xs
        liftM (as:) (revDetectBody ks bs)


findKey :: DistfixStructure a => a -> [a] -> Maybe ([a], [a])
findKey k xs = case break (nodeMatch k) xs of
    res@(_, []) -> Nothing
    (before, (_:after)) -> Just (before, after)
revFindKey :: DistfixStructure a => a -> [a] -> Maybe ([a], [a])
revFindKey k xs = do
    (b,a) <- findKey k (reverse xs)
    return (reverse a, reverse b)


------ Helpers ------

joinPriority :: Priority -> Priority -> Priority
joinPriority None y = y
joinPriority x _ = x

data Priority = Higher | Lower | None deriving (Eq)
fromOrd LT = Lower
fromOrd EQ = None
fromOrd GT = Higher

negOrd :: Ordering -> Ordering
negOrd LT = GT
negOrd EQ = EQ
negOrd GT = LT