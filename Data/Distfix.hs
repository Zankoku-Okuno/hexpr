{-| We present an algorithm for de-sugaring distributed affixes (distfixes) in a rose-like data
    structure. Distfixes are also known as "mixfixes", but I chose "dist-" because the parts of the
    affix are distributed in-order through the root, rather than mixed in (out-of-order connotation)
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

    When given a list of expressions (a node) and a distfix, the distfix may be detected within the
    list. When multiple distfixes in a scheme could match, which distfixes bind more or less
    tightly is determined by precedence and priority (see below).

    Given that a particular distfix is detected, we rewrite the list of terms into a rose-like
    structure by "extracting" the distfix keywords before its slots (in the process translating the
    disparate parts into a single item given in the definition of the distfix). Each slot is
    wrapped in its own node, but the order is not perturbed.

    Detections are made recursivly. That is, this algorithm is applied at every node in the
    structure (as made available by `unwrap`). Each node is assumed to have been wrapped in
    parenthesis during parsing, and therefore resets the precedence level. Note that rewriting only
    adds nodes to the structure, never removes them, and so we can see distfixes as adding implicit
    parenthesis, which can be quite valuble for increasing the signal-to-noise ratio in a
    programming language.


    Using the algorithm requires categorizing the input distfixes in several dimentions: topology,
    associativity, priority, and precedence. Only precedence need by specified by the user (it is
    extrinsic to any distfix), the rest are either specified in or calculated from the
    construction of the distfix at hand. We discuss these properties below:

    Slots in a distfix are always separated by keywords, but they may also be preceeded or
    followed by a keyword. The precence or absence of certain keywords is the topology of a
    distfix, and this affects the possibilities of its associativity. There are four options:
        Closed: preceded and followed by keywords (e.g. `begin_end`)
        Half-open Left: only followed by a keyword (e.g. `_!`)
        Half-open Right: only preceded by a keyword (e.g. `if_then_else_`)
        Open: neither preceded nor followed by a kwyword (e.g. `_+_`)

    As usual, there are three associativities: left-, right-, and non-associative. Open distfixes
    can take any of these three. Closed distfixes have no associtivity. Half-open left distfixes
    are always left associative, and half-open right are always right associative.

    Operators are divided into precedence levels as normal, but there are no limits on the number
    of precedence levels available for use. In the distfix table, groups of distfixes of the same
    precedence are sorted in ascending order.

    When multiple distfixes in a single precedence level are found, an attempt is made to
    disambiguate using a "priority scheme" calculated from the properties of the distfixes in
    question. Provided that one distfix has a higher priority than all the other identified
    distfixes, the highest priority distfix binds most tightly. When no such highest priority
    distfix exists, this is an error.

    The rules for calculating priority are these:
        * If both distfixes have the same associativity (left- or right-, but not non-associative),
            * The one with the "most significant" keyword "earliest" has priority:
                * Left-associative: most significant = first, earliest = leftmost
                * Right-associative: most significant = last, earliest = rightmost
            * If its a still a tie, then the one with the most keywords has priority
        * If both distfixes are closed, then they must be non-overlapping, or one must contain the other
            * It doesn't really matter which has higher priority if they don't overlap (we've chosen leftmost for now)
            * If one nests within the other, the outer has priority
            * If they overlap exactly, then the one with the most keywords has priority
        * Other pairs of matches have no priority relation


    Now, some more techincal notes:

    I'm not sure how detection and prioroty will work if the same keyword appears twice in the same
    distfix, so it's probably best to avoid that for now. Or work it out and tell me, whatever.
    Either someone will need this at some point, at we'll deal with it, or maybe I'll get bored, or
    maybe I just won't care enough relative to other problems.

    The two-typeclass system might seem a bit strange, but this is so I can avoid making the user
    involve ghc's FlexibleInstances extension. So, give an instance for `DistfixDetect SomeType`
    and `DistfixDetect a => DistfixStructure (Spine a)`, with `nodeMatch` simply unwrapping `Leaf`
    and delegating to `match`.
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
import Control.Applicative
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

newtype Match a = Match { unMatch :: (Distfix a, [a], [[a]], [a]) }
data MatchResult a = NoMatch
                   | OneMatch (Match a)
                   | Ambiguous [Match a]
data DistfixError a = AmbiguousErr [(Distfix a, [a], [[a]], [a])]
                    | LeftoverErr [a]
newtype DistfixResult' e a = Result { unResult :: Either (DistfixError e) a }
type DistfixResult a = DistfixResult' a a


------ Instances ------
instance (Show a, DistfixStructure a) => Show (DistfixError a) where
    show (AmbiguousErr matches) = headText ++ concatMap makeLine matches
        where
        headText = "Ambiguous distfix parse. Could have been one of:"
        makeLine = ("\n\t"++) . show . right . rewrite (return . rewrap) . Match
        right (Result (Right x)) = x
    show (LeftoverErr [k]) = "Leftover keyword: " ++ show k
    show (LeftoverErr ks) = "Leftover keywords:" ++ concatMap ((' ':) . show) ks


------ Main Algorithm ------
runDistfix :: DistfixStructure a => DistfixTable a -> a -> Either (DistfixError a) a
runDistfix table x = case unwrap x of
    Nothing -> return x
    Just xs -> mapM (runDistfix table) xs >>= unResult . (impl table)
    where
    impl [] xs = findLeftovers allKeywords xs
    impl table'@(row:rows) xs = case resolve row xs of
        NoMatch -> impl rows xs
        OneMatch op -> rewrite (impl table') op
        Ambiguous ops -> Result . Left . AmbiguousErr $ fmap unMatch ops
    allKeywords = nubBy nodeMatch . (concatMap . concatMap) (\(Distfix _ _ ks) -> ks) $ table

rewrite :: DistfixStructure a => ([a] -> DistfixResult a) -> Match a -> DistfixResult a
rewrite recurse (Match (Distfix distfix _ _, before, inside, after)) = do
    inside' <- liftM (rewrap . (distfix:)) (mapM recurse inside)
    recurse $ before ++ [inside'] ++ after


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

decidePriority :: Match a -> Match a -> Priority
decidePriority a@(Match (Distfix _ topA ksA, bA, iA, aA)) b@(Match (Distfix _ topB ksB, bB, iB, aB)) = case (topA, topB) of
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
        where impl (Match (Distfix _ _ ks, _, _, _)) = length ks
    -- index of leftmost keyword in the original node
    leftmostKeyword (Match (Distfix _ OpenRight _, _, inside, _)) = length (head inside)
    leftmostKeyword (Match (Distfix _ HalfOpenRight _, before, _, _)) = length before
    leftmostKeyword (Match (Distfix _ Closed _, before, _, _)) = length before
    -- index of rightmost keyword in the original node
    rightmostKeyword (Match (Distfix _ OpenLeft _, _, inside, _)) = sum (map length $ init inside) + (length (init inside) - 1)
    rightmostKeyword (Match (Distfix _ HalfOpenLeft _, _, inside, _)) = sum (map length inside) + (length inside - 1)
    rightmostKeyword (Match (Distfix _ Closed _, before, inside, _)) = length before + sum (map length inside) + length inside


------ Detection ------
findLeftovers :: DistfixStructure a => [a] -> [a] -> DistfixResult a
findLeftovers ks xs = case filter (\x -> any (nodeMatch x) ks) xs of
    [] -> Result . Right . rewrap $ xs
    errs -> Result . Left $ LeftoverErr errs

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
        HalfOpenRight -> do
            (as, bs) <- findKey (head ks) xs
            res <- detectBody (tail ks) bs
            return (as, res, [])
        HalfOpenLeft -> do
            (as, bs) <- revFindKey (last ks) xs
            res <- revDetectBody (init ks) as
            return ([], res, bs)
        OpenRight -> do
            (as, bs) <- findKey (head ks) xs
            res <- detectBody (tail ks) bs
            return ([], as:res, [])
        OpenLeft -> do
            (as, bs) <- revFindKey (last ks) xs
            res <- revDetectBody (init ks) as
            return ([], res++[bs], [])
        OpenNon -> do
            (as, bs) <- findKey (head ks) xs
            res <- detectBody (tail ks) bs
            if isJust $ detect (last res) fix
                then Nothing
                else return ([], as:res, [])
    if null `any` inside
        then Nothing
        else return $ Match (fix, before, inside, after)

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


instance Monad (DistfixResult' e) where
    return = Result . Right
    (Result x) >>= k = Result (x >>= unResult . k)
