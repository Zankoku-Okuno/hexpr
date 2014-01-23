{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
module Data.Gensym (
    -- * Generate Symbols
      Gensym(..)
    -- * Symbol Generator Monad
    , SymbolGen
    , runSymbolGen
    -- * Symbol Generator Monad Transformer
    , SymbolGenT
    , runSymbolGenT
    , MonadSymbolGen(..)
    ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State.Strict
import Control.Monad.Trans


------ Concepts ------
class Gensym s where
    genzero :: s
    nextsym :: s -> s

{- DRAGONS
    I tried to generalize Gensym here, so that you could put a symbol in a namespace
    However, what I have here need UndecidableInstances, which I didn't want, so
    On the other hand, you can always do redundant namespaceing yourself.
    When you need to display gensyms to a human, ther should be a simple algorithm (probably involving SymbolGen again)
    that should be able to reduce the gensyms actually used to something minimal.
-}
--class GenGensym a t s | t -> a where
--  genzero' :: t s
--  nextsym' :: a -> t s -> s

--instance (Gensym s) => GenGensym () Identity s where
--  genzero' = Identity genzero
--  nextsym' qual base = nextsym (runIdentity base)

class (Monad m) => MonadSymbolGen s m | m -> s where
    gensym :: m s   

--class (Monad m) => MonadGenSymbolGen a s m | m -> a, m -> s where
--  gensym' :: a -> m s

--instance (Gensym s, Monad m) => MonadGenSymbolGen () s m where
--  gensym' = const gensym

type SymbolGen s = SymbolGenT s Identity
newtype SymbolGenT s m a = SymbolGenT { unSymbolGenT :: StateT s m a }


instance (Gensym s, Monad m) => MonadSymbolGen s (SymbolGenT s m) where
    gensym = SymbolGenT $ do
        sym <- get
        modify nextsym
        return sym

runSymbolGenT :: (Gensym s, Monad m) => SymbolGenT s m a -> m a
runSymbolGenT = flip evalStateT genzero . unSymbolGenT

runSymbolGen :: (Gensym s) => SymbolGen s a -> a
runSymbolGen = runIdentity . runSymbolGenT


------- Basic Instances ------
instance Gensym Integer where
    genzero = 0
    nextsym = (+1)

instance (Monad m) => Functor (SymbolGenT s m) where
    fmap = liftM

instance (Monad m) => Applicative (SymbolGenT s m) where
    pure = return
    (<*>) = ap

instance (Monad m) => Monad (SymbolGenT s m) where
    return = SymbolGenT . return
    x >>= k = SymbolGenT $ unSymbolGenT x >>= unSymbolGenT . k

instance MonadTrans (SymbolGenT s) where
    lift = SymbolGenT . lift


------ Transformer Instances ------
    
--TODO instances for other stdlib & spinelib monads

