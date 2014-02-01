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

import qualified Data.Text as T
import Text.Parsec ( ParseError
                   , SourcePos, getPosition
                   , char, string, oneOf
                   , try, choice, option, lookAhead
                   , many, sepBy, sepEndBy, between
                   , parserZero
                   )
import Data.Hierarchy
import Data.Hexpr.Parser
import Language.EtaLisp.BasicTypes


parse :: FilePath -> String -> Either ParseError [Quasihexpr Atom]
parse source input = runHexprParser lang (parseFile parseEtaLisp) source input

parseLiterate :: FilePath -> String -> Either ParseError [Quasihexpr Atom]
parseLiterate source input = runHexprParser lang (parseLiterateFile " > " parseEtaLisp) source input

parseEtaLisp :: HexprParser () Quasihexpr Atom [Quasihexpr Atom]
parseEtaLisp = parseBareHexpr `sepEndBy` nextline

lang :: HexprLanguage Quasihexpr Atom
lang = (emptyLang ()) { _atom = map try [fieldIs, fieldAt, numLit, chrLit, strLit, name] --TODO heredoc
                      , _specialNode = [dotExpr, list, xons, strExpr, quote, quasiquote, unquote, unquoteSplicing]
                      , _indentize = [(indent, dedent), (try (string "\\\\" >> indent), dedent)]
                      , _separate = do
                                    lookAhead $ oneOf " ()#\n\t,"
                                    tokenize $ return ()
                      , _lineComment = void $ char '#'
                      , _blockComment = (void . try $ string "#{", void . try $ string "}#")
                      }


numLit :: HexprParser () Quasihexpr Atom Atom
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
    fractionNotation whole base = do
        d <- char '/' >> naturalBase base
        if d == 0 then parserZero else return (whole % d)
        
chrLit :: HexprParser () Quasihexpr Atom Atom
chrLit = do 
    (loc, Just c) <- tokWithPos $ between2 (char '\'') ((Just <$> char '\"') <|> stringLiteralChar)
    return (ChrLit loc c)

strLit :: HexprParser () Quasihexpr Atom Atom
strLit = do
    (loc, str) <- tokWithPos $ between2 (char '\"') (catMaybes <$> many stringLiteralChar)
    return (StrLit loc $ pack str)    

fieldIs :: HexprParser () Quasihexpr Atom Atom
fieldIs = uncurry FieldIs <$> tokWithPos (try $ bareField <* char ':')

fieldAt :: HexprParser () Quasihexpr Atom Atom
fieldAt = uncurry FieldAt <$> tokWithPos (char ':' >> bareField)


name :: HexprParser () Quasihexpr Atom Atom
name = do
    (loc, sym) <- tokWithPos bareName
    return $ case sym of
        "true"  -> BoolLit loc True
        "false" -> BoolLit loc False
        "λ"     -> Kw loc Lambda
        "let"   -> Kw loc Let
        "in"    -> Kw loc In
        "≡"     -> Kw loc Def
        "data"  -> Kw loc Data
        "macro" -> Kw loc Macro
        "_"     -> Kw loc AnonPoint
        "□"     -> Kw loc EmptyPat
        _       -> Var loc (intern sym)
    

list :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
list = do
    (loc, xs) <- tokWithPos $ do 
        char '['
        disableIndentation $ do 
            xs <- try (tokenize parseBareHexpr) `sepEndBy` comma
            tokenize $ char ']'
            return xs
    return $ if null xs
        then individual (Builtin loc List) `adjoin` individual (Builtin loc Nil)
        else individual (Builtin loc List) `adjoinsl` xs

xons :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
xons = do
    (loc, xs) <- tokWithPos $ do
        char '{'
        disableIndentation $ do
            xs <- try (tokenize parseBareHexpr) `sepEndBy` comma
            tokenize $ char '}'
            return xs
    return $ if null xs
        then individual (Builtin loc Xons) `adjoin` individual (Builtin loc Xil)
        else individual (Builtin loc Xons) `adjoinsl` xs

strExpr :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
strExpr = do
        (loc, x0) <- tokWithPos (char '\"' >> strSegment)
        open
        xs <- disableIndentation $ go []
        return $ individual (Builtin loc StrInterp) `adjoinsl` (x0:xs)
    where
    go acc = do
        e <- parseBareHexpr
        char ')'
        str <- strSegment
        let acc' = if empty str then [e]:acc else [e,str]:acc
        (open >> go acc') <|> (char '\"' >> (return . concat . reverse) acc')
    open = try $ string "\\("
    strSegment = do
        loc <- Loc <$> getPosition
        s <- pack . catMaybes <$> many (try stringLiteralChar)
        return $ individual (StrLit loc s)
    empty (QLeaf (StrLit _ s)) = T.null s
    empty _ = False

dotExpr :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
dotExpr = do
    (loc, e) <- tokWithPos (char '.' >> parseHexpr )
    return $ individual (Builtin loc InfixDot) `adjoin` e

quote :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
quote = do
    (loc, e) <- tokWithPos (char '\'' >> disableQuasiquotation parseHexpr)
    return $ individual (Builtin loc Quote) `adjoin` e

quasiquote :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
quasiquote = Quasiquote . snd <$> tokWithPos (char '⌜' >> withQuasiquote parseHexpr)

unquote :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
unquote = Unquote . snd <$> tokWithPos (char '⌞' >> withUnquote parseHexpr)

unquoteSplicing :: HexprParser () Quasihexpr Atom (Quasihexpr Atom)
unquoteSplicing = Splice . snd <$> tokWithPos (char '⌟' >> withUnquote parseHexpr)


bareName = parseIdentifier car cdr
    where
    car = codingChar (flip elem restrictCar)
    cdr = codingChar (flip elem restrict)
    restrict = "\"\\#.,()[]{}⌜⌞⌟:"
    restrictCar = restrict ++ "\'0123456789-"

bareField = (Left <$> naturalBase 10) <|> (Right . intern <$> bareName)

tokWithPos parser = tokenize $ do
    pos <- getPosition
    res <- parser
    return (Loc pos, res)

comma = try . tokenize $ char ','
between2 p = between p p

