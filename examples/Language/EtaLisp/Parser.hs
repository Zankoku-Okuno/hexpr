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

import Text.Parsec ( ParseError
                   , SourcePos, getPosition
                   , char, string, oneOf
                   , try, choice, option, lookAhead
                   , many, sepBy, sepEndBy, between
                   )
import Data.Hierarchy
import Data.Hexpr.Parser
import Language.EtaLisp.BasicTypes


parse :: FilePath -> String -> Either ParseError [RawEL Atom]
parse source input = runHexprParser lang (parseFile parseEtaLisp) source input

parseLiterate :: FilePath -> String -> Either ParseError [RawEL Atom]
parseLiterate source input = runHexprParser lang (parseLiterateFile " > " parseEtaLisp) source input

parseEtaLisp :: HexprParser () RawEL Atom [RawEL Atom]
parseEtaLisp = parseBareHexpr `sepEndBy` nextline

lang :: HexprLanguage RawEL Atom
lang = (emptyLang ()) { _atom = map try [unitLit, numLit, chrLit, strLit, name] --TODO heredoc
                      , _specialNode = [dotExpr, list, xons, strExpr, quote, quasiquote, unquote, unquoteSplicing]
                      , _indentize = [(indent, dedent), (try (string "\\\\" >> indent), dedent)]
                      , _separate = do
                                    lookAhead $ oneOf " ()#\n\t,"
                                    tokenize $ return ()
                      , _lineComment = void $ char '#'
                      , _blockComment = (void . try $ string "#{", void . try $ string "}#")
                      }


unitLit :: HexprParser () RawEL Atom Atom
unitLit = do
  (loc, _) <- tokWithPos $ string "()"
  return (UnitLit loc)

numLit :: HexprParser () RawEL Atom Atom
numLit = do 
    (loc, n) <- tokWithPos (try specialNumber <|> normalNumber)
    return (NumLit loc n)
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
        
chrLit :: HexprParser () RawEL Atom Atom
chrLit = do 
    (loc, Just c) <- tokWithPos $ between2 (char '\'') ((Just <$> char '\"') <|> stringLiteralChar)
    return (ChrLit loc c)

strLit :: HexprParser () RawEL Atom Atom
strLit = do
    (loc, str) <- tokWithPos $ between2 (char '\"') (catMaybes <$> many stringLiteralChar)
    return (StrLit loc $ pack str)    

name :: HexprParser () RawEL Atom Atom
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
    

list :: HexprParser () RawEL Atom (RawEL Atom)
list = (uncurry List <$>) . tokWithPos $ do 
        char '['
        disableIndentation $ do 
            xs <- tokenize parseBareHexpr `sepEndBy` comma
            tokenize $ char ']'
            return xs

xons :: HexprParser () RawEL Atom (RawEL Atom)
xons = (uncurry Xons <$>) . tokWithPos $ do
        char '{'
        disableIndentation $ do
            xs <- namedField `sepEndBy` comma
            tokenize $ char '}'
            return xs
    where
    namedField = tokenize $ do
        n <- intern <$> (char ':' >> bareName)
        e <- tokenize parseBareHexpr
        return (n, e)

strExpr :: HexprParser () RawEL Atom (RawEL Atom)
strExpr = do
        (loc, _) <- tokWithPos (char '\"')
        x0 <- strSegment
        open
        xs <- disableIndentation $ go []
        return $ StrInterp loc x0 xs
    where
    go acc = do
        e <- parseBareHexpr
        char ')'
        str <- strSegment
        let acc' = (e,str):acc
        (open >> go acc') <|> (char '\"' >> (return . reverse) acc')
    open = try $ string "\\("
    strSegment = pack . catMaybes <$> many (try stringLiteralChar)

dotExpr :: HexprParser () RawEL Atom (RawEL Atom)
dotExpr = uncurry Dot <$> tokWithPos (char '.' >> parseHexpr )

quote :: HexprParser () RawEL Atom (RawEL Atom)
quote = uncurry Code <$> tokWithPos (char '\'' >> disableQuasiquotation parseHexpr)

quasiquote :: HexprParser () RawEL Atom (RawEL Atom)
quasiquote = uncurry Quasiquote <$> tokWithPos (char '⌜' >> withQuasiquote parseHexpr)

unquote :: HexprParser () RawEL Atom (RawEL Atom)
unquote = uncurry Unquote <$> tokWithPos (char '⌞' >> withUnquote parseHexpr)

unquoteSplicing :: HexprParser () RawEL Atom (RawEL Atom)
unquoteSplicing = uncurry Splice <$> tokWithPos (char '⌟' >> withUnquote parseHexpr)


bareName = parseIdentifier car cdr
    where
    car = codingChar (flip elem restrictCar)
    cdr = codingChar (flip elem restrict)
    restrict = "\"\\#.,()[]{}⌜⌞⌟"
    restrictCar = restrict ++ "\'0123456789:"

tokWithPos parser = tokenize $ do
    pos <- getPosition
    res <- parser
    return (Loc pos, res)

comma = try . tokenize $ char ','
between2 p = between p p

