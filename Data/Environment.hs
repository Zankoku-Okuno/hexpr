module Data.Environment (
      EnvironmentT
    , Env
    , Bindings
    , EnvironmentIO
    , EnvironmentST

    --, runEnvironmentT
    , evalEnvironmentT
    --, execEnvironmentT

    , extractLocal
    , extractParent
    , copyEnv

    , find
    , bind
    , findIn
    , bindIn

    , getActiveEnv
    , withEnv
    , emptyEnv
    , freshEnv
    , localEnv
    ) where

import qualified Data.Ref as Ref

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State

import Control.Monad.ST (ST)
import Control.Monad.Identity (Identity)

--TODO implement with something faster than an AList

------ Types ------
{-| Environments are a mutable set of bindings along with an optional parent environment.
    
    When an environment is searched for a key, it first looks in its own bindings map, then looks
    in its parent's. When a binding is added to an environment, the environments own bindings are
    mutated; its ancestors remain unchanged.

    The implementation of mutable cells (allocation, reading, writing) is abstracted by @m@. See
    @Data.Ref@ for more information.
-}
data Env m k v = Env (Ref.T m (Bindings k v)) (Maybe (Env m k v))
{-| Synonym for some key-value mapping. -}
type Bindings k v = [(k, v)]

{- Perform computations involving the manipulation of @Env m k v@ terms.

    TODO talk about how there's a default and active environment
-}
newtype EnvironmentT k v m a = E { unEnvT :: StateT (Env m k v) (ReaderT (Bindings k v) m) a }

type EnvironmentIO k v = EnvironmentT k v IO
type EnvironmentST s k v = EnvironmentT k v (ST s)

type DefaultEnv k v = Bindings k v
type ActiveEnv k v = Bindings k v
newtype EnvState k v = EnvState { unState :: (DefaultEnv k v, ActiveEnv k v) }


------ Top-Level ------

--TODO we can acheive limited restarts by: run part one, flatten & return the current env, do whatever, then initialize with it again

--runEnvironment :: [(k, v)] -> EnvironmentT k v m a -> m (a, EnvState k v)
--runEnvironment env action = error "STUB"

--evalEnvironment :: (Ref.C m) => Bindings k v -> EnvironmentT k v m a -> m a
--evalEnvironment bindings (E action) = flip runReaderT bindings $ evalStateT action env

evalEnvironmentT :: (Ref.C m) => Bindings k v -> EnvironmentT k v m a -> m a
evalEnvironmentT xs (E action) = do
    env0 <- flip Env Nothing `liftM` Ref.new xs
    runReaderT (evalStateT action env0) xs

--execEnvironment :: [(k, v)] -> EnvironmentT k v m a -> m (EnvState k v)
--execEnvironment env action = liftM snd (runEnvironment env action)

--resumeEnvironment :: (Monad m) => EnvState k v -> EnvironmentT k v m ()
--resumeEnvironment = error "STUB"


------ Environment Manipulators ------
{-| Retrieve an @Env@ in every way equal to the one passed, except that the result has no parent.

    The cell in the new environment continues to reference the old, so changes in the state of one
    are mirrored in the other.
-}
extractLocal :: Env m k v -> Env m k v
extractLocal (Env cell _) = Env cell Nothing

{-| Retrieve the parent of the passed @Env@. -}
extractParent :: Env m k v -> Maybe (Env m k v)
extractParent (Env _ parent) = parent

{-| Make a deep copy of the passed environment.

    That is, both the @Env@'s own bindings cell is copied, the parent (if any) is copied, and a new
    environment is constructed of the two, which shares no state with the original with respect to
    @find@ and @bind@. Bound values are not copied, however, so state may still be shared insofar
    as the bound values have state.
-}
copyEnv :: (Ref.C m) => Env m k v -> EnvironmentT k v m (Env m k v)
copyEnv (Env cell parent) = do
    xs' <- liftHeap $ Ref.read cell
    parent' <- case parent of
        Nothing -> return Nothing
        Just parent -> Just <$> copyEnv parent
    newEnv xs' parent'


------ Binding and Lookup ------
{-| Lookup the value associated with the passed key in the current environment. See @Env@ for
    more algorithm detail.
-}
find :: (Ref.C m, Eq k) => k -> EnvironmentT k v m (Maybe v)
find k = getActiveEnv >>= \env -> findIn env k

{-| Bind the key to the value in the current environment. See @Env@ for more algorithm detail.
-}
bind :: (Ref.C m) => k -> v -> EnvironmentT k v m ()
bind k v = getActiveEnv >>= \env -> bindIn env k v
-- This is why I want something more like Murex: bind ≡ (bindIn _ k v) =<< getActiveEnv

{-| Lookup the value associated with the passed key in the passed @Env@. See @Env@ for more detail
    on the search semantics.

    We have `findIn e k v === withEnv e (find k v)`, but the implementation of @findIn@ does less
    bookkeeping internally.
-}
findIn :: (Ref.C m, Eq k) => Env m k v -> k -> EnvironmentT k v m (Maybe v)
findIn env@(Env cell Nothing) k = findInLocally env k
findIn env@(Env cell (Just parent)) k = flip maybe return <$> findIn parent k <*> findInLocally env k

{-| Bind a key to a value in the passed @Env@. See @Env@ for more detail on the search semantics.

    We have `bindIn e k v === withEnv e (bind k v)`, but the implementation of @findIn@ does less
    bookkeeping internally.
-}
bindIn :: (Ref.C m) => Env m k v -> k -> v -> EnvironmentT k v m ()
bindIn (Env cell _) k v = liftHeap $ Ref.modify cell ((k, v):)

{-| Equivalent to `findIn . extractLocal`, but it's more direct to define `findIn` in terms of this. -}
findInLocally :: (Ref.C m, Eq k) => Env m k v -> k -> EnvironmentT k v m (Maybe v)
findInLocally (Env cell _) k = lookup k <$> liftHeap (Ref.read cell)


------ Current Environment Manipulation ------
{-| Obtain a handle to the current environment. -}
getActiveEnv :: (Ref.C m) => EnvironmentT k v m (Env m k v)
getActiveEnv = liftActiveEnv get

{-| Perform an action in the given environment. -}
withEnv :: (Ref.C m) => Env m k v -> EnvironmentT k v m a -> EnvironmentT k v m a
withEnv env' action = do
    env <- getActiveEnv
    liftActiveEnv (put env') >> action << liftActiveEnv (put env)

{-| Perform an action in a new, empty, parentless environment. -}
emptyEnv :: (Ref.C m) => EnvironmentT k v m a -> EnvironmentT k v m a
emptyEnv action = do
    env' <- newEnv [] Nothing
    withEnv env' action

{-| Perform an action in a new, default, parentless environment. -}
freshEnv :: (Ref.C m) => EnvironmentT k v m a -> EnvironmentT k v m a
freshEnv action = do
    bindings <- liftDefaultEnv ask
    env' <- newEnv bindings Nothing
    withEnv env' action

{-| Perform an action in a new, initially empty environment, child to the current. -}
localEnv :: (Ref.C m) => EnvironmentT k v m a -> EnvironmentT k v m a
localEnv action = do
    env' <- newEnv [] =<< liftM Just getActiveEnv
    withEnv env' action


------ Helpers ------
infixl 1 <<
a << b = do { r <- a; b; return r }

newEnv :: (Ref.C m) => Bindings k v -> Maybe (Env m k v) -> EnvironmentT k v m (Env m k v)
newEnv xs parent = do
    env <- liftHeap $ Ref.new xs
    return $ Env env parent

liftActiveEnv :: (Ref.C m) => StateT (Env m k v) (ReaderT (Bindings k v) m) a -> EnvironmentT k v m a
liftActiveEnv = E
liftDefaultEnv :: (Ref.C m) => ReaderT (Bindings k v) m a -> EnvironmentT k v m a
liftDefaultEnv = E . lift
liftHeap :: (Ref.C m) => m a -> EnvironmentT k v m a
liftHeap = E . lift . lift


------ Instances ------
--FIXME I should only need `Functor m` constrainst here, similar for Applicative
instance (Ref.C m) => Functor (EnvironmentT k v m) where
    fmap = liftM

instance (Ref.C m) => Applicative (EnvironmentT k v m) where
    pure = return
    (<*>) = ap

instance (Ref.C m) => Monad (EnvironmentT k v m) where
    return = E . return
    x >>= k = E (unEnvT . k =<< unEnvT x)

instance MonadTrans (EnvironmentT k v) where
    lift = E . lift . lift

instance (MonadIO m, Ref.C m) => MonadIO (EnvironmentT k v m) where
    liftIO = lift . liftIO

---- TODO any stdlib monads

