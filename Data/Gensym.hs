{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
module Data.Gensym (
	  Gensym(..)
	, MonadSymbolGen(..)
	, SymbolGenT
	) where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans


------ Concepts ------
class Gensym a where
	genzero :: a
	nextsym :: a -> a

class (Monad m) => MonadSymbolGen s m | m -> s where
	gensym :: m s	

newtype SymbolGenT s m a = SymbolGenT { unSymbolGenT :: StateT s m a }

instance (Gensym s, Monad m) => MonadSymbolGen s (SymbolGenT s m) where
	gensym = SymbolGenT $ do
		sym <- get
		let sym' = nextsym sym
		put sym'
		return sym'


------- Basic Instances ------
instance Gensym Integer where
	genzero = 0
	nextsym = (+1)

--TODO functor, applicative
instance (Monad m) => Monad (SymbolGenT s m) where
	return = SymbolGenT . return
	x >>= k = SymbolGenT $ unSymbolGenT x >>= unSymbolGenT . k

instance MonadTrans (SymbolGenT s) where
	lift = SymbolGenT . lift


------ Transformer Instances ------

--TODO instances for other stdlib & spinelib monads

