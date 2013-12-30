{-| Spines are a data structure for representing and storing first-class code objects in a
    strongly-, statically-typed language.

    In an untyped language, first-class code may be represented by simple lists, which may then
    hold both atomic values as well as other lists. As code objects will need to be manipulated
    regularly, untyped lists are insuficient in a statically typed language.

    Because languages with first-class code benefit greatly from quasiquotation, we also introduce
    the quasispine along with algortihms for transforming quasispines into spines. This
    transformation requires at least certain special forms to be indicated by some marker in the
    first position of a spine node. This convention was chosen because of this tradition in Lisp
    and ought not to be too limiting for language implementors. The three special forms in
    question must
        1) create a code object from a spine,
        2) create a list from any number of values, and
        3) repackage spines analogously to list concatenation, which I call unnesting.

    In order to generate the simplest spines of code objects from quasispines, I have also
    developed a simplification algorithm which:
        Turns [quote form, value] spine into a code value
        Turns [list form, code values...] into a code value
        Turns [unnest form, code values...] into a code value

    What may not be obvious in this implementation is that Unquotes must be nested within a
    matching Quasiquote. It would be simple but tedious to lift this fact into the type system, so
    for now, I've settled with partial functions.
-}
module Data.Spine (
      Spine (..)
    , Quasispine (..)
    
    , wrapSpine
    , wrapQuasispine

    , UnQuasispine (..)
    , unQuasispine
    , SimplifySpine (..)
    , simplifySpine
    ) where
import Data.List

{-
TODO
    make Quasispine a dependent type, dependent on the level of quotation

    make my own functor instances, so I don't need compiler support
-}

------ Types ------
{-| As it turns out, a spine is little more than a rose. The original plan was different, but
    given its relationship to quasispines, sexprs, and interpretation algorithms, I may as well
    keep the name.

    An empty node is disallowed, and a one-element node ought to be equivalent to its contents
    (mirroring mathematical paretheses rather than Lisp parentheses). Unfotunately, these
    properties are not maintained by the type system, but hey, this is Haskell, not Idris.
-}
data Spine a = Leaf a
             | Node [Spine a]
    deriving Eq

{-| A quasipine extends the spine structure with quasiquotation.
    
    In addition to the usual restrictions on spines, each Unquote and Splice element must be
    contained within a matching Quasiquote element.
-}
data Quasispine a = QLeaf      a
                  | QNode      [Quasispine a]
                  | Quasiquote (Quasispine a)
                  | Unquote    (Quasispine a)
                  | Splice     (Quasispine a)
    deriving Eq


------ Data Manipulation ------
{-| Turn a list of spines into a single spine, such that singleton lists become leaves and others
    become nodes. Null lists are not permitted as a spine. -}
wrapSpine :: [Spine a] -> Spine a
wrapSpine [] = error "spine nodes must have at least one element"
wrapSpine [x] = x
wrapSpine xs = Node xs

{-| As @wrapSpine@, but for quasispines. -}
wrapQuasispine :: [Quasispine a] -> Quasispine a
wrapQuasispine [] = error "quasispine nodes must have at least one element"
wrapQuasispine [x] = x
wrapQuasispine xs = QNode xs


------ Spine Transforms ------
{-| Implement this class to allow quasispines to be transformed into spines by @unQuasispine@.
    The forms will be used like Lisp special forms: the form will appear in the first position in
    a node with the rest of the children being arguments.
-}
class UnQuasispine a where
    quoteForm  :: a
    listForm   :: a
    unnestForm :: a

{-| Transform a quasispine into a spine by replacing quasiquotation with appropriate quotation and
    constructors. The assumption is that the first element in a @Node@ may be a function or special
    form.
-}
unQuasispine :: UnQuasispine a => Quasispine a -> Spine a
unQuasispine = trans . impl . normalize
    where
    impl :: (UnQuasispine a) => Quasispine a -> Quasispine a
    impl (QNode xs)                  = QNode (map impl xs)
    impl (Quasiquote (QLeaf x))      = QNode [QLeaf quoteForm, QLeaf x]
    impl (Quasiquote (QNode xs))     = unquasiquoteNode xs
    impl (Quasiquote (Quasiquote x)) = pushQuote . pushQuote $ x
    impl (Quasiquote (Unquote x))    = impl x
    impl (Quasiquote (Splice x))     = impl x
    impl x = x
    trans :: Quasispine a -> Spine a
    trans (QLeaf x)  = Leaf x
    trans (QNode xs) = Node (map trans xs)
    trans (Quasiquote _) = error "tried to translate quasiquote"
    normalize :: Quasispine a -> Quasispine a
    normalize a = case a of
        QLeaf x       -> a
        QNode [x]     -> normalize x
        QNode xs      -> QNode (map normalize xs)
        Quasiquote x  -> Quasiquote (normalize x)
        Unquote x     -> Unquote (normalize x)
        Splice x      -> Splice (normalize x)
    unquasiquoteNode xs = case groupBy splitSplices xs of
            [xs] | isSplice xs -> error "unquote splicing really unimplemented" --TODO um, what?
                 | otherwise   -> QNode (QLeaf listForm : map pushQuote xs)
            xss -> QNode (QLeaf unnestForm : map createSpliceList xss)
        where
            splitSplices x y = case (x, y) of 
                (Splice _, _) -> False
                (_, Splice _) -> False
                _ -> True
            createSpliceList xs = if isSplice xs
                then (let [x] = xs in pushQuote x)
                else QNode (QLeaf listForm : map pushQuote xs)
            isSplice xs = case xs of { [Splice _] -> True; _ -> False }
    pushQuote :: (UnQuasispine a) => Quasispine a -> Quasispine a
    pushQuote = impl . Quasiquote

{-| Implement this class to allow use of @simplifySpine@, which reduces the complexity of some
    spines generated by @unQuasiSpine@.
-}
class (Eq a, UnQuasispine a) => SimplifySpine a where
    isCode   :: a -> Bool
    toCode   :: Spine a -> a
    fromCode :: a -> Spine a

{-| The algorithm of @unQuasispine@ usually produces spines that are more complex than is
    necessary. This function factors @quoteForm@s, @listForm@s and @unnestForm@s to eliminate
    redundancy.
-}
simplifySpine :: SimplifySpine a => Spine a -> Spine a
simplifySpine x = case x of
        Leaf x       -> Leaf x
        Node (x:[])  -> simplifySpine x
        Node (q:[x]) | q == Leaf quoteForm -> toCode' $ simplifySpine x
        Node (l:xs)  | l == Leaf listForm  ->
                        let xs' = map simplifySpine xs
                        in if isCode' `all` xs'
                          then toCode' . simplifySpine . Node $ map fromCode' xs'
                          else Node (l:xs')
        Node (c:xs)  | c == Leaf unnestForm ->
                        let xs' = map simplifySpine xs
                        in if isCode' `all` xs'
                          then toCode' . Node $ concatMap (unnest . fromCode') xs'
                          else Node (c:xs')
        Node xs   -> Node (map simplifySpine xs)
    where
    isCode' (Leaf x) = isCode x
    isCode' _ = False
    toCode' = Leaf . toCode
    fromCode' (Leaf x) = fromCode x
    unnest (Leaf x) = [Leaf x]
    unnest (Node xs) = xs


------ Instances ------
--TODO this won't work if there's internal structure in the Leaves
--perhaps if I use `toCode :: Spine a -> Spine a`, then we needn't worry about internal structure so much`
instance Functor Spine where
    fmap f (Leaf x) = Leaf (f x)
    fmap f (Node xs) = Node $ (map . fmap) f xs

instance Functor Quasispine where
    fmap f (QLeaf x) = QLeaf (f x)
    fmap f (QNode xs) = QNode $ (map . fmap) f xs
    fmap f (Quasiquote x) = Quasiquote (fmap f x)
    fmap f (Unquote x) = Unquote (fmap f x)
    fmap f (Splice x) = Splice (fmap f x)
