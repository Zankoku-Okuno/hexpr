module Language.EtaLisp.BasicTypes (
      module Data.Ratio
    , module Data.Maybe
    , module Data.List
    , Text, pack, unpack
    , module Data.Symbol
    , (<$>), (<*>), (<*), (*>), (<|>)
    , module Control.Monad
    , Loc(..)
    , Atom(..)
    , HNum(..)
    , Keyword(..)
    , RawEL(..)
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


data Loc = Loc SourcePos
         | Implicit

data Atom = UnitLit Loc
          | NumLit  Loc HNum
          | ChrLit  Loc Char
          | StrLit  Loc Text
          | Var     Loc Symbol
          | Kw      Loc Keyword
data HNum = HNum Rational
          | Inf | NegZero | NegInf | NaN
data Keyword = Lambda | Let | In
             | Def | Data | Macro
             | AnonPoint | EmptyPat

data RawEL a = Atom a
             | Apply [RawEL a]
             | Dot Loc (RawEL a)
             | List Loc [RawEL a]
             | Xons Loc [(Symbol, RawEL a)]
             | StrInterp Loc Text [(RawEL a, Text)]
             | Code Loc (RawEL a)
             | Quasiquote Loc (RawEL a)
             | Unquote Loc (RawEL a)
             | Splice Loc (RawEL a)


instance Hierarchy RawEL where
    individual = Atom
    
    conjoin (Apply as) (Apply bs) = Apply (as ++ bs)
    conjoin a (Apply bs) = Apply (a:bs)
    conjoin (Apply as) b = Apply (as++[b])
    conjoin a b = Apply [a, b]

    adjoinsl x [] = x
    adjoinsl x xs = Apply (x:xs)

instance Openable RawEL where
    openAp (f, _) (Atom x) = Atom (f x)
    openAp (_, f) (Apply xs) = Apply (f xs)
    openAp f (Dot loc e) = Dot loc (f `openAp` e)
    openAp f (List loc es) = List loc (map (openAp f) es)
    openAp f (Xons loc es) = Xons loc (map (\(s,e) -> (s, f `openAp` e)) es)
    openAp f (StrInterp loc x0 xs) = StrInterp loc x0 (map (\(e, x) -> (f `openAp` e, x)) xs)
    openAp f (Code loc e) = Code loc (f `openAp` e)
    openAp f (Quasiquote loc e) = Quasiquote loc (f `openAp` e)
    openAp f (Unquote loc e) = Unquote loc (f `openAp` e)
    openAp f (Splice loc e) = Splice loc (f `openAp` e)


instance Show Atom where
    show (UnitLit _) = "()"
    show (NumLit _ (HNum n)) | denominator n == 1 = show (numerator n)
                           | otherwise = show (numerator n) ++ '/' : show (denominator n)
    show (NumLit _ Inf) = "∞"
    show (NumLit _ NegZero) = "-0"
    show (NumLit _ NegInf) = "-∞"
    show (NumLit _ NaN) = "NaN"
    show (ChrLit _ c) = show c
    show (StrLit _ s) = show s
    show (Var _ sym) = unintern sym
    show (Kw _ kw) = show kw
instance Show Keyword where
    show Lambda = "λ"
    show Let = "let"
    show In = "in"
    show Def = "≡"
    show Data = "data"
    show Macro = "macro"
    show AnonPoint = "_"
    show EmptyPat = "□"

instance Show a => Show (RawEL a) where
    show (Atom x) = show x
    show (Apply xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Dot _ e) = "." ++ show e
    show (List _ xs) = "[" ++ intercalate ", " (map show xs) ++ "]"
    show (Xons _ xs) = "{" ++ intercalate ", " (map showXonsPair xs) ++ "}"
    show (StrInterp _ x0 xs) = "\"" ++ unpack x0 ++ concatMap showInterpPair xs ++ "\""
    show (Code _ x) = '\'' : show x
    show (Quasiquote _ x) = "⌜" ++ show x
    show (Unquote _ x) = "⌞" ++ show x
    show (Splice _ x) = "⌟" ++ show x
showXonsPair (sym, val) = ":" ++ unintern sym ++ " " ++ show val
showInterpPair (e@(Apply _), str) = "\\" ++ show e ++ unpack str
showInterpPair (e, str) = "\\(" ++ show e ++ ")" ++ unpack str