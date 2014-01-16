{-| We present an algorithm for de-sugaring distributed affixes (/distfixes/) in a rose-like data
    structure. Distfixes are also known as /mixfixes/, but I chose /dist-/ because the parts of
    the affix are distributed in-order through the root, rather than mixed in (out-of-order
    connotation) with the root. Now then, let's actually describe a distfix in detail:
  
    By /rose-like/ data structure, we mean any type @t@ such that when an element of @t@ can be
    'unwrap'ped into a @[t]@, we can perform rewrites according to our distfix algorithm
    and 'rewrap' the result. If a particular element cannot be 'unwrap'ped, then it will be
    left alone during rewriting. Of course, this library was meant to operate on 'Spines' and
    'Quasispines', but it could just as well work on a plain list or rose, as well as anything else
    you're willing to mangle into shape.

    A distributed affix consists of a number of alternating /keywords/ and /slots/. While keywords
    should match exactly one leaf node, slots can consume multiple nodes (leaves or branches)
    during a detection. If we denote slots by underscores and keywords by some reasonable
    programming language identifier (w/o underscores), then some representative distfix examples
    might be @_+_@, @_?_:_@, @_!@, @if_then_else_@, and @while_do_end@.

    Using the algorithm requires categorizing the input distfixes in several dimensions:
    /topology/, /associativity/, /priority/, and /precedence/. Only precedence need by specified by
    the user (it is extrinsic to any distfix), the rest are either specified in or calculated from
    the distfix at hand. We discuss these properties below:

    Slots in a distfix are always separated by keywords, but they may also be a leading and/or
    trailing keyword in a distfix. The presence or absence of certain keywords is the
    /topology/ of a distfix, and this affects the possibilities of its /associativity/.
    There are four options:
      
        * /Closed/: preceded and followed by keywords (e.g. @begin_end@)
        
        * /Half-open Left/: only followed by a keyword (e.g. @_!@)
        
        * /Half-open Right/: only preceded by a keyword (e.g. @if_then_else_@)
        
        * /Open/: neither preceded nor followed by a keyword (e.g. @_+_@)

    As usual, there are three /associativities/: /left-/, /right-/, and /non-associative/. Open
    distfixes can take any of these three. Closed distfixes have no associativity. Half-open left
    distfixes are always left associative, and half-open right are always right associative.

    Operators are divided into /precedence/ levels as normal, but there are no limits on the number
    of precedence levels available for use. In the distfix table, groups of distfixes of the same
    precedence are sorted in descending order.

    When given a list of expressions (the contents of an 'unwrap'ped node) and a distfix, the
    distfix may be /detected/ within the list. When multiple distfixes in a single precedence
    level are detected at once, an attempt is made to /select/ exactly one of the detected
    distfixes using a /priority scheme/ calculated from the properties of the distfixes in
    question. Provided that one distfix has a higher priority than all the other detected
    distfixes, the highest priority distfix binds least tightly (and is therefore selected first).

    The rules for calculating priority are these:
        
        * If both distfixes have the same associativity (left- or right-, but not non-associative),
            the one with the \"most significant\" keyword \"earliest\" has priority:
                for left-associative, most significant means first and earliest means leftmost;
                for right-associative, most significant means last, earliest means rightmost.
            If its a still a tie, then the one with the most keywords has priority.

        * If both distfixes are closed, then they must be non-overlapping, or one must contain the
        other.
            It doesn't really matter which has higher priority if they don't overlap
                (as it happens, we've chosen leftmost for now).
            If one nests within the other, the outer has priority.
            If they overlap exactly, then the one with the most keywords has priority.
        
        * Other pairs of matches have no priority distinction.

    Given that a particular distfix is detected and selected for rewriting, we rewrite the list of
    terms by /extracting/ the distfix from its slots. Specifically, the rewritten list consists of
    some element (given in the 'Distfix' definition) followed by each (filled) slot in order and
    'rewrap'ped in its own node. The re-written list is finally 'rewrap'ped and placed back in
    its original context.

    Detections are made recursively. The details are unimportant except that this algorithm is
    applied at every branch in the structure /as made available/ by 'unwrap' and the recursion
    respects precedence and priority. Each branch is assumed to have been enclosed by parenthesis
    during parsing, and therefore 'unwrap'ping resets the precedence level. Note that rewriting
    only adds branches to the structure, never removes them, and so we can see distfixes as
    adding implicit parenthesis, which can be quite valuable as a conservative tool for
    increasing the signal-to-noise ratio in a programming language.

    Now for some technical notes:

    I'm not sure how detection and priority will work if the same keyword appears twice in the same
    distfix, so it's probably best to avoid that for now. Or work it out and tell me, whatever.
    Either someone will eventually need this, at which point we'll deal with it, or maybe I'll get
    bored, or maybe I just won't care enough relative to other problems.

    The two-typeclass system might seem a bit strange, but this is so I can avoid making the user
    involve ghc's @FlexibleInstances@ extension. So, give an instance for
    @'DistfixElement' SomeType@ and @'DistfixElement' a => 'DistfixStructure' ('Spine' a)@, with
    'nodeMatch' simply unwrapping 'Leaf' and delegating to 'match'.
-}
module Data.Distfix (
    -- * Data Structures
      Distfix(..)
    , Shape(..)
    , DistfixTable
    -- * Classes
    , DistfixStructure(..)
    , DistfixElement(..)
    -- * User Space
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
{-| These data structures can be de-structured in a rose-like fashion. See the module description
    for detail on the meaning of \"rose-like\".

    There is one law:

        [Inverse] @maybe node (\(xs, rewrap) -> rewrap xs) (unwrap node) === node@

    In other words, if you can unwrap a node, then rewrapping will perform the inverse.
-}
class DistfixStructure f where
    {-| Unpack a branch node into a list of that branch's children
        and a rewrapping function. -}
    unwrap :: f -> Maybe ([f], [f] -> f)

    {-| Workaround so I can give an instance of Show (DistfixError a).
    -}
    defaultRewrap :: [f] -> f
    
    {-| Whereas 'match' operates on elements of the structure, 'nodeMatch' is really just
        boilerplate that extracts an element and calls 'match' on it.

        For example, we might write
        
@
    instance 'DistfixDetect' a => 'DistfixStructure' ('Spine' a)
        nodeMatch ('Leaf' x) ('Leaf' y) = match x y
        nodeMatch _ _ = False
@

        Very probably, it would not make sense to allow a non-leaf node to match anything (by
        implication, disallowing non-leaf keywords).
    -}
    nodeMatch :: f -> f -> Bool
{-| This class is used for matching instead of 'Eq' so that certain components of the data might be
    ignored. For example, if @a = (SourcePos, b)@ then the @SourcePos@ should clearly be ignored
    during matching.
-}
class DistfixElement a where
    {-| Whether the two elements are equal with respect to matching a keyword. -}
    match :: a -> a -> Bool

{-| A distfix consists of
        1) a rewrite element (to precede the slots when extracting),
        2) a topology and associativity, which is actually merged into a single datatype 'Shape'
            because the choice of associativity is not independent of topology, and
        3) a non-empty list of keywords, each implicitly separated by a slot.

    In case a distfix has a closed topology, its list of keywords must actually be at least two
    elements long (one for the open keyword, and one for the close keyword).

    For more detail on these components, see the module documentation.
-}
data Distfix a = Distfix a Shape [a]
{-| Information on both topology and associativity.

    The two properties are merged into one datatype because choice of one limits choice of the
    other. The constructors should make the possibilities clear enough, but the module
    documentation might better present the reasoning involved.
-}
data Shape = Closed | HalfOpenRight | HalfOpenLeft | OpenRight | OpenLeft | OpenNon
{-| A list, in descending order of precedence (ascending of binding tightness) of groups of
    Distfixes.

    How tightly distfixes within a group bind relative to one another is determined by priority
    (see the module description). Although ambiguous grammars are accepted, it might be best to
    avoid forcing the user to make lots of priority calculations just to determine if they need to
    insert disambiguating parenthesis.
-}
type DistfixTable a = [[Distfix a]]

newtype Detection a = Detection { unMatch :: (Distfix a, [a], [[a]], [a]) }
data MatchResult a = NoMatch
                   | OneMatch (Detection a)
                   | Ambiguous [Detection a]
type DistfixResult a = DistfixResult' a a
-- I only threw @DistfixResult'@ in here so I can make a monad. @DistfixResult@ is the more important one
newtype DistfixResult' e a = Result { unResult :: Either (DistfixError e) a }

{-| Report reasons for error in recognizing distfixes. There are two causes of error: 

    [Ambiguity] When there is no single detection that has higher precedence or priority within a
    set of detections made in a node, this is an ambiguous parse. Note that ambiguous grammars are
    allowed in this scheme, but should this ambiguity manifest itself in an input, that input is
    not recognized. Really, this is pretty spiffy: distfixes admit specification fairly near to an
    arbitrary context-free grammar, but the algorithm will excise ambiguity only where it needs to,
    completely side-stepping the problem of whether a given grammar is ambiguous.

    [Leftovers] Once we've detected all the keywords possible in a node, we need to ensure there
    are no leftover keywords. If there were, this would probably indicate a user forgetting a
    keyword. For example, suppose @[|_|]@ were a distfix then  @[| a ]@ would obtain a LeftoverErr.

    There's some fuzziness between 'AmbiguousErr' and 'LeftoverErr'. To illustrate, suppose we have
    @_<_@ and @_<=_@ but not @_<=_<_@ as a distfix, then both @a < b < c@ and @a <= b < c@ will be
    errors. The first will result in leftovers, and the second in ambiguity. It would make sense if
    they were both 'AmbiguousErr', but doing so under the current structure would sacrifice some
    efficiency (and possibly complicate matters). Still, at least everything that /should/ be an
    error /is/ an error.
-}
data DistfixError a = AmbiguousErr [(Distfix a, [a], [[a]], [a])]
                    | LeftoverErr [a]


------ Instances ------
instance (Show a, DistfixStructure a) => Show (DistfixError a) where
    show (AmbiguousErr matches) = headText ++ concatMap makeLine matches
        where
        headText = "Ambiguous distfix parse. Could have been one of:"
        makeLine = ("\n\t"++) . show . right . extract (return . defaultRewrap) defaultRewrap . Detection
        right (Result (Right x)) = x
    show (LeftoverErr [k]) = "Leftover keyword: " ++ show k
    show (LeftoverErr ks) = "Leftover keywords:" ++ concatMap ((' ':) . show) ks


------ Main Algorithm ------
{-| Given a table of distfixes and some input structure, apply the distfix detection/extraction
    algorithm.

    The algorithm may fail with a 'DistfixError'. The module description explains successful
    results in more detail.
-}
runDistfix :: DistfixStructure a => DistfixTable a -> a -> Either (DistfixError a) a
runDistfix table x = case unwrap x of
    Nothing -> return x
    Just (xs, rewrap) -> mapM (runDistfix table) xs >>= unResult . (impl rewrap table)
    where
    impl rewrap [] xs = findLeftovers rewrap allKeywords xs
    impl rewrap table'@(row:rows) xs = case select row xs of
        NoMatch -> impl rewrap rows xs
        OneMatch op -> extract (impl rewrap table') rewrap op
        Ambiguous ops -> Result . Left . AmbiguousErr $ fmap unMatch ops
    allKeywords = nubBy nodeMatch . (concatMap . concatMap) (\(Distfix _ _ ks) -> ks) $ table

{-| It's a pretty weird mutual-recursion thing going on between runDistfix.impl and extract. 
    See, we obviously have to recurse on the inner nodes, but then we also need to recurse on the
    reconstructed node, in case of nodes like `a + if p then conseq else alt`

    I'm basically passing in `recurse` as a specialized delimited continuation. There's another
    function that uses extract, so I couldn't just put extract in the closure with impl.
    I'm pretty sure it's necessary to pass the recursion in anyway (but I can't remember why).
-}
extract :: DistfixStructure a => ([a] -> DistfixResult a) -> ([a] -> a) -> Detection a -> DistfixResult a
extract recurse rewrap (Detection (Distfix distfix _ _, before, inside, after)) = do
    inside' <- rewrap . (distfix:) <$> mapM recurse inside
    recurse $ before ++ [inside'] ++ after


------ Selection ------
{-| Given a bunch of distfixes (at the same precedence level), try to find an unambiguous distfix
    parse within a list.
-}
select :: DistfixStructure a => [Distfix a] -> [a] -> MatchResult a
select ops xs = impl detectAll []
    where
    detectAll = catMaybes $ map (detect xs) ops
    impl [] eqSet = case eqSet of
        []  -> NoMatch
        [x] -> OneMatch x
        xs  -> Ambiguous xs
    impl (x:xs) eqSet = if      is Lower  then impl xs eqSet
                        else if is Higher then impl xs [x]
                        else                   impl xs (x:eqSet)
        where is = (`elem` map (decidePriority x) eqSet)

{-| Given two detections, give the relative priority of the first to the second. -}
decidePriority :: Detection a -> Detection a -> Priority
decidePriority a@(Detection (Distfix _ topA ksA, bA, iA, aA)) b@(Detection (Distfix _ topB ksB, bB, iB, aB)) = case (topA, topB) of
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
    _                              -> Same
    where
    decideRight = leftmost `joinPriority` mostKeywords
        where leftmost = fromOrd . negOrd $ comparing leftmostKeyword a b
    decideLeft = rightmost `joinPriority` mostKeywords
        where rightmost = fromOrd $ comparing rightmostKeyword a b
    decideClosed = leftmostNoOverlap `joinPriority` outermost `joinPriority` (if exactOverlap then mostKeywords else Same)
        where
        leftmostNoOverlap = if aR < bL then Higher else if bR < aL then Lower else Same
        outermost = case (compare aL bL, compare aR bR) of
            (LT, GT) -> Higher -- `a b b a`
            (GT, LT) -> Lower  -- `b a a b`
            (LT, EQ) -> Higher -- `a b ab`
            (GT, EQ) -> Lower  -- `b a ab`
            (EQ, LT) -> Lower  -- `ab a b`
            (EQ, GT) -> Higher -- `ab b a`
            _ -> Same
        exactOverlap = aL == bL && aR == bR
        aL = leftmostKeyword a
        aR = rightmostKeyword a
        bL = leftmostKeyword b
        bR = rightmostKeyword b
    mostKeywords = fromOrd $ comparing impl a b
        where impl (Detection (Distfix _ _ ks, _, _, _)) = length ks
    -- index of leftmost keyword in the original node
    leftmostKeyword (Detection (Distfix _ OpenRight _, _, inside, _)) = length (head inside)
    leftmostKeyword (Detection (Distfix _ HalfOpenRight _, before, _, _)) = length before
    leftmostKeyword (Detection (Distfix _ Closed _, before, _, _)) = length before
    -- index of rightmost keyword in the original node
    rightmostKeyword (Detection (Distfix _ OpenLeft _, _, inside, _)) = sum (map length $ init inside) + (length (init inside) - 1)
    rightmostKeyword (Detection (Distfix _ HalfOpenLeft _, _, inside, _)) = sum (map length inside) + (length inside - 1)
    rightmostKeyword (Detection (Distfix _ Closed _, before, inside, _)) = length before + sum (map length inside) + length inside


------ Detection ------
{-| Once all possible detections have been found in a node, use this to repack. -}
findLeftovers :: DistfixStructure a => ([a] -> a) -> [a] -> [a] -> DistfixResult a
findLeftovers rewrap ks xs = case filter (\x -> nodeMatch x `any` ks) xs of
    [] -> Result . Right . rewrap $ xs
    errs -> Result . Left $ LeftoverErr errs

{-| FIXME MAYBE This guy ignores the possibility of several matches of the same keyword, which may
    lead to weird error messages? Not sure, but if weird error messages don't haunt us, this is
    more efficient by a fair margin.
-}
detect :: DistfixStructure a => [a] -> Distfix a -> Maybe (Detection a)
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
            (as, bs) <- findKey (head ks) xs -- find the first one, so the following ones get wrapped in implicit parens
            res <- detectBody (tail ks) bs
            return ([], as:res, [])
        OpenLeft -> do
            (as, bs) <- revFindKey (last ks) xs -- find the last one, so the preceding ones get wrapped in implicit parens
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
        else Just $ Detection (fix, before, inside, after)

{-| recognize keyword-slot pairs left-to-right, so use as a continuation after stripping away leading/trailing keywords -}
detectBody :: DistfixStructure a => [a] -> [a] -> Maybe [[a]]
detectBody [] xs = Just [xs]
detectBody (k:ks) xs = do
    (as, bs) <- findKey k xs
    liftM (as:) (detectBody ks bs)
{-| as detect body, but right-to-left, for left-associative things -}
revDetectBody :: DistfixStructure a => [a] -> [a] -> Maybe [[a]]
revDetectBody ks xs = liftM (map reverse) $ impl (reverse ks) (reverse xs)
    where
    impl [] xs = Just [xs]
    impl (k:ks) xs = do
        (bs, as) <- revFindKey k xs
        liftM (as:) (revDetectBody ks bs)

{-| Get the parts of a list (before, after) the given keyword. Start from the left. -}
findKey :: DistfixStructure a => a -> [a] -> Maybe ([a], [a])
findKey k xs = case nodeMatch k `break` xs of
    res@(_, []) -> Nothing
    (before, (_:after)) -> Just (before, after)
{-| As findKey, but start from right. -}
revFindKey :: DistfixStructure a => a -> [a] -> Maybe ([a], [a])
revFindKey k xs = do
    (b,a) <- findKey k (reverse xs)
    return (reverse a, reverse b)


------ Helpers ------
{-| if the first way of determining priority works, take it, otherwise try the second way -}
joinPriority :: Priority -> Priority -> Priority
joinPriority Same y = y
joinPriority x _ = x

data Priority = Higher | Lower | Same deriving (Eq)
fromOrd LT = Lower
fromOrd EQ = Same
fromOrd GT = Higher

negOrd :: Ordering -> Ordering
negOrd LT = GT
negOrd EQ = EQ
negOrd GT = LT

instance Functor (DistfixResult' e) where
    fmap = liftM

instance Applicative (DistfixResult' e) where
    pure = return
    (<*>) = ap

instance Monad (DistfixResult' e) where
    return = Result . Right
    (Result x) >>= k = Result (x >>= unResult . k)
