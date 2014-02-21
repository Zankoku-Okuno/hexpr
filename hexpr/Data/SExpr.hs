{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Data.Sexpr (
      Sexpr(..)
    , SexprToHexpr(..)
    , sexprToHexpr
    ) where

import Data.Hierarchy
import Data.Hexpr


data Sexpr p a = Atom p a | Sexpr p [Sexpr p a]

instance Hierarchy Sexpr p where
    getPos (Atom p _) = p
    getPos (Sexpr p _) = p

    individual = Atom

    conjoin p (Sexpr _ as) (Sexpr _ bs) = Sexpr p (as++bs)
    conjoin p a (Sexpr _ bs) = Sexpr p (a:bs)
    conjoin p (Sexpr _ as) b = Sexpr p (as++[b])
    conjoin p a b = Sexpr p [a, b]

    adjoinsl p x xs = Sexpr p (x:xs)

    adjoins = Sexpr

instance Openable (Sexpr p) where
    openAp (f, _) (Atom p x) = Atom p (f x)
    openAp (_, f) (Sexpr p xs) = Sexpr p (f xs)


class SexprToHexpr a where
    xformNull :: p -> Hexpr p a
    xformNull = error "Empty sexprs are disallowed"
    xformSingleton :: Sexpr p a -> Hexpr p a

    xformDeepAtom :: a -> a
    xformDeepAtom = id

sexprToHexpr :: (SexprToHexpr a) => Sexpr p a -> Hexpr p a
sexprToHexpr (Atom p x) = Leaf p (xformDeepAtom x)
sexprToHexpr (Sexpr p []) = xformNull p
sexprToHexpr (Sexpr p [x]) = xformSingleton x
sexprToHexpr (Sexpr p xs) = Branch p (map sexprToHexpr xs)

