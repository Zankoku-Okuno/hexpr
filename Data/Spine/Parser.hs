module Data.Spine.Parser (
      QuasiSpineParser (..)
    ) where

import Data.Spine

import Text.Parsec
import Text.Parsec.Char

type QuasiSpineState = (Int, Int)
type Parser = Parsec String QuasiSpineState
startState :: QuasiSpineState
startState = (0, 0)

class (UnQuasiSpine a) => QuasiSpineParser a where
    parseAtom       :: Parser (QuasiSpine a)
    parseQuote      :: Parser (QuasiSpine a)
    parseQuasiquote :: Parser (QuasiSpine a)
    parseUnquote    :: Parser (QuasiSpine a)
    parseQuasiSpine :: String -> FilePath -> Either ParseError (Spine a)
    parseQuasiSpine path input =
        case runP impl startState path input of
            Left err  -> Left err
            Right val -> Right $ unQuasiSpine val


impl :: QuasiSpineParser a => Parser (QuasiSpine a)
impl = fail ""