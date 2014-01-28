{-
Begin with Lisp. Change from sexprs to hexprs, change from conses to xonses,
add data abstraction, support unicode source code, make macros (mostly) hygenic.
Sprinkle with syntactic sugar. Bake at 200ºC for fifteen minutes, and no eggs.
-}
module Language.EtaLisp (run) where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either

import Language.EtaLisp.BasicTypes
import Language.EtaLisp.Parser

run :: FilePath -> IO (Either String ())
run filepath = runEitherT $ do
    content <- liftIO $ readFile filepath
    raw <- case parse filepath content of
        Left err -> left $ show err
        Right val -> return val
    void . liftIO $ mapM print raw