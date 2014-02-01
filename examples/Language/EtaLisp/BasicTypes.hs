module Language.EtaLisp.BasicTypes (
      module Data.Ratio
    , module Data.Maybe
    , module Data.List
    , Text, pack, unpack
    , module Data.Symbol
    , module Data.Hexpr
    , (<$>), (<*>), (<*), (*>), (<|>)
    , module Control.Monad
    , Loc(..)
    , Atom(..)
    , HNum(..)
    , Keyword(..)
    , Builtin(..)
    ) where

import Data.Ratio
import Data.Maybe
import Data.List
import Data.Text (Text, pack, unpack)
import Data.Symbol
import Control.Applicative ((<$>), (<*>), (*>), (<*), (<|>))
import Control.Monad

import Text.Parsec (SourcePos)
import Data.Hierarchy
import Data.Hexpr

type FiniteTypeIndex = Either Integer Symbol
data Loc = Loc SourcePos
         | Implicit

data Atom = BoolLit Loc Bool
          | NumLit  Loc HNum
          | ChrLit  Loc Char
          | StrLit  Loc Text
          | Var     Loc Symbol
          | FieldIs Loc FiniteTypeIndex 
          | FieldAt Loc FiniteTypeIndex
          | Kw      Loc Keyword
          | Builtin Loc Builtin
data HNum = HNum Rational
          | Inf | NegZero | NegInf | NaN
data Keyword = Lambda | Let | In
             | Def | Data | Macro
             | AnonPoint | EmptyPat
data Builtin = Quote
             | Nil | List
             | Xil | Xons
             | InfixDot
             | StrInterp


instance Show Atom where
    show (BoolLit _ b) = if b then "true" else "false"
    show (NumLit _ (HNum n)) | denominator n == 1 = show (numerator n)
                             | otherwise = show (numerator n) ++ '/' : show (denominator n)
    show (NumLit _ Inf) = "∞"
    show (NumLit _ NegZero) = "-0"
    show (NumLit _ NegInf) = "-∞"
    show (NumLit _ NaN) = "NaN"
    show (ChrLit _ c) = show c
    show (StrLit _ s) = show s
    show (FieldIs _ (Left n)) = show n ++ ":"
    show (FieldIs _ (Right s)) = unintern s ++ ":"
    show (FieldAt _ (Left n)) = ':' : show n
    show (FieldAt _ (Right s)) = ':' : unintern s
    show (Var _ sym) = unintern sym
    show (Kw _ kw) = show kw
    show (Builtin _ bi) = '#' : show bi
instance Show Keyword where
    show Lambda = "λ"
    show Let = "let"
    show In = "in"
    show Def = "≡"
    show Data = "data"
    show Macro = "macro"
    show AnonPoint = "_"
    show EmptyPat = "□"
instance Show Builtin where
    show Quote = "quote"
    show Nil = "nil"
    show List = "list"
    show Xil = "xil"
    show Xons = "xons"
    show InfixDot = "."
    show StrInterp = "str"

instance Show a => Show (Quasihexpr a) where
    show (QLeaf x) = show x
    show (QBranch xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Quasiquote x) = "⌜" ++ show x
    show (Unquote x) = "⌞" ++ show x
    show (Splice x) = "⌟" ++ show x

