module Data.Environment (
      EnvironmentT
    , Env
    , MEnv
    , Bindings
    , EnvironmentIO
    , EnvironmentST

    --, runEnvironmentT
    , evalEnvironmentT
    --, execEnvironmentT

    , extractLocal
    , extractParent
    , copyEnv
    , copyLocalEnv

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

import Data.Monoid
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State

import Control.Monad.ST (ST)
import Control.Monad.Identity (Identity)

--TODO implement with something faster than an AList

------ Types ------
{-| Environments, also called contexts, are a set of bindings along with an optional parent
    environment.
    
    When an environment is searched for a key, it first looks in its own bindings map, then looks
    in its parent's. When a binding is added to an environment, the environments own bindings are
    updated; its ancestors remain unchanged.
-}
data Env k v = Env (Bindings k v) (Maybe (Env k v))
--FIXME I actually can merge Maps, so I may as well do it that way instead of using parents

{-| Where 'Env' represents immutable (mathematical) environments, 'MEnv' represent mutable
    environments. Mutable environments are useful for accumulating recursive bindings.
    
    The implementation of mutable cells (allocation, reading, writing) is abstracted by @m@. See
    @Data.Ref@ for more information.
-}
data MEnv m k v = MEnv (Ref.T m (Bindings k v)) (Maybe (MEnv m k v))
{-| Synonym for some key-value mapping. -}
type Bindings k v = [(k, v)]

{- Perform computations involving the manipulation of @MEnv m k v@ terms.

    TODO talk about how there's a default and active environment
-}
newtype EnvironmentT k v m a = E { unEnvT :: StateT (MEnv m k v) (ReaderT (Bindings k v) m) a }

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
--evalEnvironment bindings = runIdentity . evalEnvironmentT bindings

evalEnvironmentT :: (Ref.C m) => Bindings k v -> EnvironmentT k v m a -> m a
evalEnvironmentT xs (E action) = do
    env0 <- flip MEnv Nothing `liftM` Ref.new xs
    runReaderT (evalStateT action env0) xs

--execEnvironment :: [(k, v)] -> EnvironmentT k v m a -> m (EnvState k v)
--execEnvironment env action = liftM snd (runEnvironment env action)

--resumeEnvironment :: (Monad m) => EnvState k v -> EnvironmentT k v m ()
--resumeEnvironment = error "STUB"


------ Environment Manipulators ------
{-| Retrieve an @MEnv@ in every way equal to the one passed, except that the result has no parent.

    The cell in the new environment continues to reference the old, so changes in the state of one
    are mirrored in the other.
-}
extractLocal :: MEnv m k v -> MEnv m k v
extractLocal (MEnv cell _) = MEnv cell Nothing

{-| Retrieve the parent of the passed @MEnv@. -}
extractParent :: MEnv m k v -> Maybe (MEnv m k v)
extractParent (MEnv _ parent) = parent

{-| Make a deep copy of the passed environment.

    That is, both the @MEnv@'s own bindings cell is copied, the parent (if any) is copied, and a new
    environment is constructed of the two, which shares no state with the original with respect to
    @find@ and @bind@. Bound values are not copied, however, so state may still be shared insofar
    as the bound values have state.
-}
copyEnv :: (Ref.C m) => MEnv m k v -> EnvironmentT k v m (MEnv m k v)
copyEnv (MEnv cell parent) = do
    xs' <- liftHeap $ Ref.read cell
    parent' <- case parent of
        Nothing -> return Nothing
        Just parent -> Just <$> copyEnv parent
    newEnv xs' parent'

{-| Make a shallow copy of the passed environment

    That is, only the @MEnv@'s own bindings cell is copied; the parent (if any) is not copied.
    A new environment is constructed of the two, which shares only enough state with the original
    so that writes to the new do not affect the original, and only writes to the parents of the
    original are available (modulo shadowing) in the new. Bound values are not copied, however,
    so state may also be shared insofar as the bound values have state.
-}
copyLocalEnv :: (Ref.C m) => MEnv m k v -> EnvironmentT k v m (MEnv m k v)
copyLocalEnv (MEnv cell parent) = do
    xs' <- liftHeap $ Ref.read cell
    newEnv xs' parent

{-| Create an immutable environment from a snapshot of the passed mutable environment. -}
closeEnv :: (Ref.C m) => MEnv m k v -> EnvironmentT k v m (Env k v)
closeEnv (MEnv cell parent) = do
    xs <- liftHeap $ Ref.read cell
    parent' <- case parent of 
        Just p -> Just <$> closeEnv p
        Nothing -> return Nothing
    return $ Env xs parent'
    

------ Binding and Lookup ------
{-| Lookup the value associated with the passed key in the current environment. See @MEnv@ for
    more algorithm detail.
-}
find :: (Ref.C m, Eq k) => k -> EnvironmentT k v m (Maybe v)
find k = getActiveEnv >>= \env -> findIn env k

{-| Bind the key to the value in the current environment. See @MEnv@ for more algorithm detail.
-}
bind :: (Ref.C m) => k -> v -> EnvironmentT k v m ()
bind k v = getActiveEnv >>= \env -> bindIn env k v
-- This is why I want something more like Murex: bind ≡ (bindIn _ k v) =<< getActiveEnv

{-| Lookup the value associated with the passed key in the passed @MEnv@. See @MEnv@ for more detail
    on the search semantics.

    We have `findIn e k v === withEnv e (find k v)`, but the implementation of @findIn@ does less
    bookkeeping internally.
-}
findIn :: (Ref.C m, Eq k) => MEnv m k v -> k -> EnvironmentT k v m (Maybe v)
findIn env@(MEnv cell Nothing) k = findInLocally env k
findIn env@(MEnv cell (Just parent)) k = flip maybe return <$> findIn parent k <*> findInLocally env k

{-| Bind a key to a value in the passed @MEnv@. See @MEnv@ for more detail on the search semantics.

    We have `bindIn e k v === withEnv e (bind k v)`, but the implementation of @findIn@ does less
    bookkeeping internally.
-}
bindIn :: (Ref.C m) => MEnv m k v -> k -> v -> EnvironmentT k v m ()
bindIn (MEnv cell _) k v = liftHeap $ Ref.modify cell ((k, v):)

{-| Equivalent to `findIn . extractLocal`, but it's more direct to define `findIn` in terms of this. -}
findInLocally :: (Ref.C m, Eq k) => MEnv m k v -> k -> EnvironmentT k v m (Maybe v)
findInLocally (MEnv cell _) k = lookup k <$> liftHeap (Ref.read cell)


------ Current Environment Manipulation ------
{-| Obtain a handle to the current environment. -}
getActiveEnv :: (Ref.C m) => EnvironmentT k v m (MEnv m k v)
getActiveEnv = liftActiveEnv get

{-| Perform an action in the given environment. -}
withEnv :: (Ref.C m) => MEnv m k v -> EnvironmentT k v m a -> EnvironmentT k v m a
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

newEnv :: (Ref.C m) => Bindings k v -> Maybe (MEnv m k v) -> EnvironmentT k v m (MEnv m k v)
newEnv xs parent = do
    env <- liftHeap $ Ref.new xs
    return $ MEnv env parent

liftActiveEnv :: (Ref.C m) => StateT (MEnv m k v) (ReaderT (Bindings k v) m) a -> EnvironmentT k v m a
liftActiveEnv = E
liftDefaultEnv :: (Ref.C m) => ReaderT (Bindings k v) m a -> EnvironmentT k v m a
liftDefaultEnv = E . lift
liftHeap :: (Ref.C m) => m a -> EnvironmentT k v m a
liftHeap = E . lift . lift


------ Instances ------
instance Monoid (Env k v) where
    mempty = Env [] Nothing
    mappend env (Env xs Nothing) | null xs   = env
                                 | otherwise = Env xs (Just env)
    mappend env (Env xs (Just parent)) | null xs   = env `mappend` parent
                                       | otherwise = Env xs (Just $ env `mappend` parent)
--TODO monoid for MEnv


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

