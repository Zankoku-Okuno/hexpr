module Control.Monad.Errors (
      Errors
    , runErrors
    , ErrorsT
    , runErrorsT
    , err
    , recover
    , recover_
    , mapRecover
    ) where

import Data.Monoid
import Data.Either
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad.Trans
import Control.Monad.Trans.Either


type Errors e a = ErrorsT e Identity a
newtype ErrorsT e m a = ErrorsT { unErrors :: m (Maybe e -> (Maybe a, Maybe e)) }

runErrors :: (Monoid e) => Errors e a -> Either e a
runErrors = runIdentity . runErrorsT

runErrorsT :: (Monad m, Monoid e) => ErrorsT e m a -> m (Either e a)
runErrorsT action = do
    innerAction <- unErrors action
    let res = innerAction Nothing
    return $ case res of
        (Just val, Nothing) -> Right val
        (_, Just errs) -> Left errs
        (Nothing, Nothing) -> error "Control.Monad.Errors: internal error"


err :: (Monad m, Monoid e) => e -> ErrorsT e m a
err msg = ErrorsT . return $ \e -> (Nothing, e <> Just msg)

choice :: (Monad m, Monoid e) => e -> [ErrorsT e m a] -> ErrorsT e m a
choice e0 [] = err e0
choice e0 (a:as) = do
    res <- lift $ runErrorsT a
    case res of
        Left e0 -> choice e0 as
        Right val -> return val

recover :: (Monad m, Monoid e) => a -> ErrorsT e m a -> ErrorsT e m a
recover replacement action = ErrorsT $ do
    res <- runErrorsT action
    return $ case res of
        Left err -> \e -> (Just replacement, e <> Just err)
        Right val -> \e -> (Just val, e)

recover_ :: (Monad m, Monoid e) => ErrorsT e m a -> ErrorsT e m ()
recover_ action = recover () (const () <$> action)

mapRecover :: (Monad m, Monoid e) => [ErrorsT e m a] -> ErrorsT e m [Maybe a]
mapRecover actions = mapM (recover Nothing . (Just <$>)) actions


instance (Monad m, Monoid e) => Functor (ErrorsT e m) where
    fmap = liftM

instance (Monad m, Monoid e) => Applicative (ErrorsT e m) where
    pure = return
    (<*>) = ap

instance (Monad m, Monoid e) => Monad (ErrorsT e m) where
    return x = ErrorsT . return $ \e -> (Just x, e)
    x >>= k = ErrorsT $ do
        eRes <- runErrorsT x
        case eRes of
            Left err -> return $ \e -> (Nothing, e <> Just err)
            Right val -> unErrors $ k val

instance (Monoid e) => MonadTrans (ErrorsT e) where
    lift x = ErrorsT $ do
        x' <- x
        return $ \e -> (Just x', e)

instance (MonadIO m, Monoid e) => MonadIO (ErrorsT e m) where
    liftIO = lift . liftIO
