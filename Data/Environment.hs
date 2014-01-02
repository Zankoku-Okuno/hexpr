module Data.Environment (
      EnvironmentT
    , Environment
    , Env
    , Bindings

    --, runEnvironment
    , evalEnvironment
    --, execEnvironment

    , find
    , findLocal
    , bind

    , getCurrentEnv
    , withEnv
    , emptyEnv
    , freshEnv
    , localEnv
    ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.ST.Trans
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader

--TODO implement with something faster than an AList

------ Types ------

data Env s k v = Env (STRef s (Bindings k v)) (Maybe (Env s k v))
type Bindings k v = [(k, v)]

--WARNING use as directed by the Control.Monad.State.Trans warning
newtype EnvironmentT s k v m a = E { unEnvT ::  StateT (Env s k v)
                                               (STT s
                                               (ReaderT (Bindings k v)
                                                m))
                                                a }

type Environment s k v = EnvironmentT s k v Identity


------ Top-Level ------

--TODO we can acheive limited restarts by: run part one, flatten & return the current env, do whatever, then initialize with it again

--runEnvironment :: [(k, v)] -> EnvironmentT s k v m a -> m (a, EnvState k v)
--runEnvironment env action = error "STUB"

evalEnvironment :: (Monad m) => Bindings k v -> EnvironmentT s k v m a -> ReaderT (Bindings k v) m a
evalEnvironment env = runST . evalStateT startEnv . unEnvT
    where
    startEnv = error "STUB"

--execEnvironment :: [(k, v)] -> EnvironmentT s k v m a -> m (EnvState k v)
--execEnvironment env action = liftM snd (runEnvironment env action)

--resumeEnvironment :: (Monad m) => EnvState k v -> EnvironmentT s k v ()
--resumeEnvironment = error "STUB"

--TODO run/eval/exec in Identity monad


------ Binding and Lookup ------
find :: (Monad m) => k -> EnvironmentT s k v m (Maybe v)
find = error "STUB"

findLocal :: (Monad m) => k -> EnvironmentT s k v m (Maybe v)
findLocal = error "STUB"

bind :: (Monad m) => (k, v) -> EnvironmentT s k v m ()
bind = error "STUB"

--TODO MAYBE lookup/bind in given environment, so the user doesn't have to write `withEnv e . find` all the time


------ Current Environment Manipulation ------
{-| Obtain a handle to the current environment. -}
getCurrentEnv :: (Monad m) => EnvironmentT s k v m (Env s k v)
getCurrentEnv = liftCurrentEnv get

{-| Perform an action in the given environment. -}
withEnv :: (Monad m) => Env s k v -> EnvironmentT s k v m a -> EnvironmentT s k v m a
withEnv env' action = do
    env <- getCurrentEnv
    liftCurrentEnv (put env') >> action << liftCurrentEnv (put env)

{-| Perform an action in a new, empty, parentless environment. -}
emptyEnv :: (Monad m) => EnvironmentT s k v m a -> EnvironmentT s k v m a
emptyEnv action = do
    env' <- newEnv [] Nothing
    withEnv env' action

{-| Perform an action in a new, default, parentless environment. -}
freshEnv :: (Monad m) => EnvironmentT s k v m a -> EnvironmentT s k v m a
freshEnv action = do
    bindings <- liftDefaultEnv ask
    env' <- newEnv bindings Nothing
    withEnv env' action

{-| Perform an action in a new, initially empty environment, child to the current. -}
localEnv :: (Monad m) => EnvironmentT s k v m a -> EnvironmentT s k v m a
localEnv action = do
    env' <- newEnv [] =<< liftM Just getCurrentEnv
    withEnv env' action


------ Helpers ------
infixl 1 <<
a << b = do { r <- a; b; return r }

newEnv :: (Monad m) => Bindings k v -> Maybe (Env s k v) -> EnvironmentT s k v m (Env s k v)
newEnv xs parent = do
    env <- liftHeap $ newSTRef xs
    return $ Env env parent

liftCurrentEnv :: (Monad m) => StateT (Env s k v) (STT s (ReaderT (Bindings k v) m)) a -> EnvironmentT s k v m a
liftCurrentEnv = E
liftHeap :: (Monad m) => STT s (ReaderT (Bindings k v) m) a -> EnvironmentT s k v m a
liftHeap = E . lift
liftDefaultEnv :: (Monad m) => ReaderT (Bindings k v) m a -> EnvironmentT s k v m a
liftDefaultEnv = E . lift . lift

------ Instances ------
--TODO give an instance for Functor and Applicative, but this would require hacking at the code for STT

instance Monad m => Monad (EnvironmentT s k v m) where
    return = E . return
    x >>= k = E (unEnvT . k =<< unEnvT x)

instance MonadTrans (EnvironmentT s k v) where
    lift = E . lift . lift . lift

instance MonadIO m => MonadIO (EnvironmentT s k v m) where
    liftIO = lift . liftIO

---- TODO any stdlib monads


