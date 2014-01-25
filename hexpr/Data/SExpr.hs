module Data.Sexpr (
	  Sexpr(..)
	, SexprToHexpr(..)
	, sexprToHexpr
	) where

import Data.Hexpr


data Sexpr a = Atom a | Sexpr [Sexpr a]


class SexprToHexpr a where
	xformNull :: Hexpr a
	xformNull = error "Empty sexprs are disallowed"
	xformSingleton :: a -> Hexpr a

	xformDeepAtom :: a -> a
	xformDeepAtom = id

sexprToHexpr :: (SexprToHexpr a) => Sexpr a -> Hexpr a
sexprToHexpr (Atom x) = Leaf (xformDeepAtom x)
sexprToHexpr (Sexpr []) = xformNull
sexprToHexpr (Sexpr [Atom x]) = xformSingleton x
sexprToHexpr (Sexpr [xs]) = sexprToHexpr xs
sexprToHexpr (Sexpr xs) = Branch (map sexprToHexpr xs)

