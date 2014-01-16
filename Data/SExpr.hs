module Data.SExpr (
	  SExpr(..)
	) where

import Data.Spine


data SExpr a = Atom a | SExpr [SExpr a]


class SExprToSpine a where
	xformNull :: Spine a
	xformNull = error "Empty sexprs are disallowed"
	xformSingleton :: a -> Spine a

	xformDeepAtom :: a -> a
	xformDeepAtom = id

sexprToSpine :: (SExprToSpine a) => SExpr a -> Spine a
sexprToSpine (Atom x) = Leaf (xformDeepAtom x)
sexprToSpine (SExpr []) = xformNull
sexprToSpine (SExpr [Atom x]) = xformSingleton x
sexprToSpine (SExpr [xs]) = sexprToSpine xs
sexprToSpine (SExpr xs) = Branch (map sexprToSpine xs)

