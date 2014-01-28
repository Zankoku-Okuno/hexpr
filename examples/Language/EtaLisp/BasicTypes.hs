module Language.EtaLisp.BasicTypes where

import Data.Ratio
import Data.Text (Text)
import Data.List
import Text.Parsec (SourcePos)
import Data.Hexpr

type Loc = (SourcePos, SourcePos)

data Literal = UnitLit
             | NumLit HNum
             | ChrLit Char
             | StrLit Text

data HNum = HNum Rational
          | Inf | NegZero | NegInf | NaN

data Keyword = Lambda | Let | In
             | Def | Data | Macro
             | AnonPoint | EmptyPat


instance Show a => Show (Quasihexpr a) where
    show (QLeaf x) = show x
    show (QBranch xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Quasiquote x) = "⌜" ++ show x
    show (Unquote x) = "⌞" ++ show x
    show (Splice x) = "⌟" ++ show x

instance Show Literal where
    show UnitLit = "()"
    show (NumLit (HNum n)) | denominator n == 1 = show (numerator n)
                           | otherwise = show (numerator n) ++ '/' : show (denominator n)
    show (NumLit Inf) = "∞"
    show (NumLit NegZero) = "-0"
    show (NumLit NegInf) = "-∞"
    show (NumLit NaN) = "NaN"
    show (ChrLit c) = show c
    show (StrLit s) = show s

instance Show Keyword where
    show Lambda = "λ"
    show Let = "let"
    show In = "in"
    show Def = "≡"
    show Data = "data"
    show Macro = "macro"
    show AnonPoint = "_"
    show EmptyPat = "□"