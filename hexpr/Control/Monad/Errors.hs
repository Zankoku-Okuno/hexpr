{-| In many error-checking algorithms, it is desireable to report several
    errors rather than simply terminate on detecting the first error.

    Where 'Either' and 'Error' terminates on the first error, 'Errors' can
    recover at specified points and continue error-checking. Even after a
    recovery, the prior errors are logged. If any errors occured during
    error-checking, this si an error in the whole computation.
-}
module Control.Monad.Errors (
    -- * Errors Monad
      Errors
    , runErrors
    -- * Error Reporting Functions
    , err
    , err1
    , choice
    , recover
    , recover_
    , mapRecover
    -- ** Hoisting Functions
    , hoistMaybe
    , hoistEither
    , hoistEither1
    -- * Errors Transformer
    , ErrorsT
    , runErrorsT
    ) where

import Data.Monoid
import Data.Either
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad.Trans
import Control.Monad.Trans.Either hiding (hoistEither)


{-| Shortcut for 'ErrorsT' over the 'Identity' monad. -}
type Errors e a = ErrorsT e Identity a
{-| Computations that can collect multiple errors. -}
newtype ErrorsT e m a = ErrorsT { unErrors :: m (Maybe e -> (Maybe a, Maybe e)) }

{-| Perform an error-reporting computation. -}
runErrors :: (Monoid e) => Errors e a -> Either e a
runErrors = runIdentity . runErrorsT

{-| Perform the error reporting part of a computation. -}
runErrorsT :: (Monad m, Monoid e) => ErrorsT e m a -> m (Either e a)
runErrorsT action = do
    innerAction <- unErrors action
    let res = innerAction Nothing
    return $ case res of
        (Just val, Nothing) -> Right val
        (_, Just errs) -> Left errs
        (Nothing, Nothing) -> error "Control.Monad.Errors: internal error"


{-| Report an error. -}
err :: (Monad m, Monoid e) => e -> ErrorsT e m a
err msg = ErrorsT . return $ \e -> (Nothing, e <> Just msg)

{-| Report one error accumulating in a list. -}
err1 :: (Monad m) => e -> ErrorsT [e] m a
err1 = err . (:[])

{-| Try several alternatives (in order), but if none succeed, raise the passed error. -}
choice :: (Monad m, Monoid e) => e -> [ErrorsT e m a] -> ErrorsT e m a
choice e0 [] = err e0
choice e0 (a:as) = do
    res <- lift $ runErrorsT a
    case res of
        Left e0 -> choice e0 as
        Right val -> return val

{-| If the action returns an error, relpace the result with a default.
    The error is still logged and reported at the end of the computation. -}
recover :: (Monad m, Monoid e) => a -> ErrorsT e m a -> ErrorsT e m a
recover replacement action = ErrorsT $ do
    res <- runErrorsT action
    return $ case res of
        Left err -> \e -> (Just replacement, e <> Just err)
        Right val -> \e -> (Just val, e)

{-| As 'recover', but any successful result value does not matter. -}
recover_ :: (Monad m, Monoid e) => ErrorsT e m a -> ErrorsT e m ()
recover_ action = recover () (const () <$> action)

{-| Perform many error checks, recovering between each. The value at each index of the output
    list corresponds to the index of the input computation list. Error values are 'Nothing'
    in the output, successful values are wrapped in 'Just'. -}
mapRecover :: (Monad m, Monoid e) => [ErrorsT e m a] -> ErrorsT e m [Maybe a]
mapRecover actions = mapM (recover Nothing . (Just <$>)) actions


{-| Turn a 'Maybe' computation into an 'ErrorsT' computation. -}
hoistMaybe :: (Monad m, Monoid e) => e -> Maybe a -> ErrorsT e m a
hoistMaybe e = maybe (err e) return

{-| Turn an 'Either' computation into an 'ErrorsT' computation. -}
hoistEither :: (Monad m, Monoid e) => Either e a -> ErrorsT e m a
hoistEither = either err return

{-| Turn an 'Either' computation into an 'ErrorsT' computation when accumulating a list. -}
hoistEither1 :: (Monad m) => Either e a -> ErrorsT [e] m a
hoistEither1 = either err1 return


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
