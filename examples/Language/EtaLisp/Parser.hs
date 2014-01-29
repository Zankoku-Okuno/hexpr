{-
Begin with Lisp. Change from sexprs to hexprs, change from conses to xonses,
add data abstraction, support unicode source code, make macros (mostly) hygenic.
Sprinkle with syntactic sugar. Bake at 200ºC for fifteen minutes, and no eggs.
-}
module Language.EtaLisp.Parser (
      Atom(..)
    , parse
    , parseLiterate
    ) where

import Data.Ratio
import Data.Text (Text, pack, unpack)
import qualified Data.Text as T
import Data.Symbol
import Data.Maybe
import Data.Either
import Data.List

import Control.Applicative ((<$>), (<*>), (*>), (<*))
import Control.Monad

import Text.Parsec ( ParseError
                   , SourcePos, getPosition
                   , char, string, oneOf
                   , try, (<|>), choice, option, lookAhead
                   , many, sepBy, sepEndBy, between
                   )

import Data.Hexpr
import Data.Hexpr.Parser
import Language.EtaLisp.BasicTypes


data Atom = Lit       Loc Literal 
          | Var       Loc Symbol
          | List      Loc [Quasihexpr Atom]
          | Xons      Loc [Quasihexpr Atom] [(Symbol, Quasihexpr Atom)]
          --TODO string interpolation
          | Dot       Loc (Quasihexpr Atom)
          | Kw        Loc Keyword

parse :: FilePath -> String -> Either ParseError [Quasihexpr Atom]
parse source input = runHexprParser lang (parseFile parseEtaLisp) source input

parseLiterate :: FilePath -> String -> Either ParseError [Quasihexpr Atom]
parseLiterate source input = runHexprParser lang (parseLiterateFile " > " parseEtaLisp) source input

parseEtaLisp :: HexprParser () Quasihexpr Atom [Quasihexpr Atom]
parseEtaLisp = parseBareHexpr `sepEndBy` nextline


lang :: HexprLanguage Quasihexpr Atom
lang = (emptyLang ()) { _atom = map try [unitLit, numLit, chrLit, strLit, name, list, xons, dotExpr] --TODO heredoc
                      , _specialNode = [quote, quasiquote, unquote, unquoteSplicing]
                      , _indentize = [(indent, dedent), (try (string "\\\\" >> indent), dedent)]
                      , _separate = do
                                    lookAhead $ oneOf " ()#\n\t,"
                                    tokenize $ return ()
                      , _lineComment = void $ char '#'
                      , _blockComment = (void . try $ string "#{", void . try $ string "}#")
                      }

unitLit :: HexprParser () Quasihexpr Atom Atom
unitLit = do
  (loc, _) <- tokWithPos $ string "()"
  return $ Lit loc UnitLit

numLit :: HexprParser () Quasihexpr Atom Atom
numLit = do 
    (loc, n) <- tokWithPos (try specialNumber <|> normalNumber)
    return $ Lit loc (NumLit n)
    where
    specialNumber = choice $ map try [ string "∞"  >> lookAhead (try separate) >> return Inf
                                     , string "-∞" >> lookAhead (try separate) >> return NegInf
                                     , string "NaN"  >> lookAhead (try separate) >> return NaN
                                     ]
    normalNumber = do
        sign <- option 1 (char '-' >> return (-1))
        (whole, base) <- naturalLiteral
        n <- choice [ scientificNotation whole base
                    , fractionNotation whole base
                    , return (whole % 1)
                    ]
        if n == (0 % 1) && sign == -1
            then return NegZero
            else return $ HNum (sign * n)
    scientificNotation whole base = do
        mantissa <- mantissaLiteral base
        exponent <- exponentLiteral
        return $ ((whole % 1) + mantissa) * exponent
    fractionNotation whole base = char '/' >> (whole %) <$> naturalBase base
        

chrLit :: HexprParser () Quasihexpr Atom Atom
chrLit = do 
    (loc, Just c) <- tokWithPos $ between2 (char '\'') ((Just <$> char '\"') <|> stringLiteralChar)
    return $ Lit loc (ChrLit c)

strLit :: HexprParser () Quasihexpr Atom Atom
strLit = do
    (loc, str) <- tokWithPos $ between2 (char '\"') (catMaybes <$> many stringLiteralChar)
    return $ Lit loc (StrLit $ pack str)    

name :: HexprParser () Quasihexpr Atom Atom
name = do
    (loc, sym) <- tokWithPos bareName
    return $ case sym of
        "λ"     -> Kw loc Lambda
        "let"   -> Kw loc Let
        "in"    -> Kw loc In
        "≡"     -> Kw loc Def
        "data"  -> Kw loc Data
        "macro" -> Kw loc Macro
        "_"     -> Kw loc AnonPoint
        "□"     -> Kw loc EmptyPat
        --TODO more keywords?
        _ -> Var loc (intern sym)
    
list :: HexprParser () Quasihexpr Atom Atom
list = (uncurry List <$>) . tokWithPos $ do 
        char '['
        disableIndentation $ do 
            xs <- tokenize parseBareHexpr `sepEndBy` comma
            tokenize $ char ']'
            return xs

xons :: HexprParser () Quasihexpr Atom Atom
xons = do
    (loc, (numbered, named)) <- tokWithPos $ do
        char '{'
        disableIndentation $ do
            xs <- (try numberedField <|> namedField) `sepEndBy` comma
            tokenize $ char '}'
            return $ partitionEithers xs
    return $ Xons loc numbered named
    where
    numberedField :: HexprParser () Quasihexpr Atom (Either (Quasihexpr Atom) (Symbol, Quasihexpr Atom))
    numberedField = tokenize (Left <$> parseBareHexpr)
    namedField :: HexprParser () Quasihexpr Atom (Either (Quasihexpr Atom) (Symbol, Quasihexpr Atom))
    namedField = tokenize $ do
        char ':'
        n <- intern <$> bareName
        e <- tokenize parseBareHexpr
        return $ Right (n, e)

dotExpr :: HexprParser () Quasihexpr Atom Atom
dotExpr = uncurry Dot <$> tokWithPos (char '.' >> parseHexpr )

quote :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
quote = Quasiquote <$> (char '\'' >> disableQuasiquotation parseHexpr)

quasiquote :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
quasiquote = Quasiquote <$> (char '⌜' >> withQuasiquote parseHexpr)

unquote :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
unquote = Unquote <$> (char '⌞' >> withUnquote parseHexpr)

unquoteSplicing :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
unquoteSplicing = Splice <$> (char '⌟' >> withUnquote parseHexpr)


bareName = parseIdentifier car cdr
    where
    car = codingChar (flip elem restrictCar)
    cdr = codingChar (flip elem restrict)
    restrict = "\"\\#.,()[]{}⌜⌞⌟"
    restrictCar = restrict ++ "\'0123456789:"

tokWithPos parser = tokenize $ do
    pos0 <- getPosition
    res <- parser
    pos <- getPosition
    return ((pos0, pos), res)

comma = try . tokenize $ char ','
between2 p = between p p


instance Show Atom where
    show (Lit _ x) = show x
    show (Var _ sym) = unintern sym
    show (List _ xs) = "[" ++ intercalate ", " (map show xs) ++ "]"
    show (Xons _ [] nxs) = "{" ++ intercalate ", " (map showXonsPair nxs) ++ "}"
    show (Xons _ pxs []) = "{" ++ intercalate ", " (map show pxs) ++ "}"
    show (Xons _ pxs nxs) = "{" ++ intercalate ", " (map show pxs ++ map showXonsPair nxs) ++ "}"
    show (Dot _ e) = "." ++ show e
    show (Kw _ kw) = show kw
showXonsPair (sym, val) = ":" ++ unintern sym ++ " " ++ show val

