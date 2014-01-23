module Main where

import Data.List
import System.IO
import System.Environment
import System.Directory
import System.Exit
import Control.Applicative
import Control.Monad
import qualified Language.SystemT as SystemT

main :: IO ()
main = do
    args <- getArgs
    case args of
        [langname, filename] -> do
            missing <- not <$> doesFileExist filename
            when missing $ die $ "File `" ++ filename ++ "' does not exist."
            result <- case langname of
            	"t" -> SystemT.run filename
            	_ -> return . Left $ "Unrecognized language `" ++ langname ++ "'. Try one of: " ++ intercalate ", " ["t", "pcf", "f"]
            case result of
                Right () -> putStrLn "Goodbyte, cruel world!" >> exitSuccess
                Left errmsg -> die errmsg
        _ -> do
            progname <- getProgName
            die $ "Usage: " ++ progname ++ " <language> <file>"

die msg = do
    hPutStrLn stderr msg
    exitFailure