{-| We provide a monad which can be used to gather multiple errors and warnings
    during computation.
-}
module Control.Monad.Report (
      ReportT
    , runReportT
    , Report
    , runReport
    , warn
    , err
    , reportWithin
    ) where

import Data.Either
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad.Trans


{-| Computations that can report multiple warnings and errors. -}
newtype ReportT e w m a = ReportT { unReport :: WriterT [Either w e] m a }

{-| Run a computation that can report multiple warnings and errors. -}
runReportT :: (Monad m) => ReportT e w m a -> m ([w], Either [e] a)
runReportT (ReportT action) = do
    (result, acc) <- runWriterT action
    let (warnings, errors) = partitionEithers acc
    return $ if null errors
        then (warnings, Right result)
        else (warnings, Left errors)

{-| Log a warning. -}
warn :: (Monad m) => w -> ReportT e w m ()
warn x = ReportT $ tell [Left x]

{-| Log an error. -}
err :: (Monad m) => e -> ReportT e w m ()
err x = ReportT $ tell [Right x]

{-| Gather the warnings and errors from a sub-report.
    The sub-report is logged in the main report as well.
-}
reportWithin :: (Monad m) => ReportT e w m a -> ReportT e w m (a, ([w], [e]))
reportWithin (ReportT action) = do
    result@(_, (warnings, errors)) <- lift $ do
        (result, acc) <- runWriterT action
        return (result, partitionEithers acc)
    mapM warn warnings
    mapM err errors
    return result

{-| Synonym for report computations over 'Identity'. -}
type Report e w = ReportT e w Identity

{-| Run a reporting computation over 'Identity'. -}
runReport :: Report e w a -> ([w], Either [e] a)
runReport = runIdentity . runReportT


instance (Monad m) => Functor (ReportT e w m) where
    fmap = liftM

instance (Monad m) => Applicative (ReportT e w m) where
    pure = return
    (<*>) = ap

instance (Monad m) => Monad (ReportT e w m) where
    return = ReportT . return
    x >>= k = ReportT $ unReport x >>= unReport . k

instance MonadTrans (ReportT e w) where
    lift = ReportT . lift

instance (MonadIO m) => MonadIO (ReportT e w m) where
    liftIO = lift . liftIO
