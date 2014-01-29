module Data.Sexpr (
      Sexpr(..)
    , SexprToHexpr(..)
    , sexprToHexpr
    ) where

import Data.Hierarchy
import Data.Hexpr


data Sexpr a = Atom a | Sexpr [Sexpr a]

instance Hierarchy Sexpr where
    individual = Atom

    conjoin (Sexpr as) (Sexpr bs) = Sexpr (as++bs)
    conjoin a (Sexpr bs) = Sexpr (a:bs)
    conjoin (Sexpr as) b = Sexpr (as++[b])
    conjoin a b = Sexpr [a, b]

    adjoinsl x xs = Sexpr (x:xs)

    unsafeAdjoins = Sexpr

instance Openable Sexpr where
    openAp (f, _) (Atom x) = Atom (f x)
    openAp (_, f) (Sexpr xs) = Sexpr (f xs)


class SexprToHexpr a where
    xformNull :: Hexpr a
    xformNull = error "Empty sexprs are disallowed"
    xformSingleton :: Sexpr a -> Hexpr a

    xformDeepAtom :: a -> a
    xformDeepAtom = id

sexprToHexpr :: (SexprToHexpr a) => Sexpr a -> Hexpr a
sexprToHexpr (Atom x) = Leaf (xformDeepAtom x)
sexprToHexpr (Sexpr []) = xformNull
sexprToHexpr (Sexpr [x]) = xformSingleton x
sexprToHexpr (Sexpr xs) = Branch (map sexprToHexpr xs)

