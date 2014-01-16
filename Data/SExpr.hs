module Data.SExpr (
	  SExpr(..)
	) where

data SExpr a = Atom a | SExpr [SExpr a]


--TODO SExpr to Spine