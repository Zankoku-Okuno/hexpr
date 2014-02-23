{-# LANGUAGE FlexibleContexts #-}
module Language.Parse where

import Control.Monad
import Control.Applicative ((<$>), (<*>), (*>), (<*))

import Data.Maybe
import Data.Ratio
import Data.Char
import Text.Parsec ( ParsecT
                   , satisfy, char, oneOf, eof
                   , try, (<?>), parserZero)
import qualified Text.Parsec as P



------ Composable Combinators ------
--FIXME put this in Parsec.Combinators.Composable
string :: (Monad m, P.Stream s m Char) => String -> ParsecT s u m String
string = try . P.string

lookAhead :: (Monad m, P.Stream s m t) => ParsecT s u m a -> ParsecT s u m a
lookAhead = try . P.lookAhead

manyTill :: (Monad m, P.Stream s m t) => ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m [a]
manyTill p e = P.manyTill p (lookAhead e)

manyThru :: (Monad m, P.Stream s m t) => ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m [a]
manyThru p e = P.manyTill p (try e)

(<|>) :: (Monad m, P.Stream s m t) => ParsecT s u m a -> ParsecT s u m a -> ParsecT s u m a
a <|> b = try a P.<|> b

choice :: (Monad m, P.Stream s m t) => [ParsecT s u m a] -> ParsecT s u m a
choice = P.choice . map try

--TODO sepBy &co


------ Useful Combinators ------
many2 :: (Monad m, P.Stream s m t) => ParsecT s u m a -> ParsecT s u m a -> ParsecT s u m [a]
many2 p ps = do
    car <- p
    cdr <- P.many ps
    return (car:cdr)

between2 :: (Monad m, P.Stream s m t) => ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m b
between2 e p = P.between e e p

isEof :: (Show t, Monad m, P.Stream s m t) => ParsecT s u m Bool
isEof = (eof >> return True) P.<|> return False


spaces1 :: (Monad m, P.Stream s m Char) => ParsecT s u m ()
spaces1 = void $ P.many1 P.spaces

charICase :: (Monad m, P.Stream s m Char) => Char -> ParsecT s u m Char
charICase c = satisfy $ (== toLower c) . toLower

stringICase :: (Monad m, P.Stream s m Char) => String -> ParsecT s u m String
stringICase str = try $ mapM charICase str


------ Parsing Identifiers ------
blacklistChar :: (Monad m, P.Stream s m Char) => (Char -> Bool) -> ParsecT s u m Char
blacklistChar p = satisfy $ \c -> not (p c) && case generalCategory c of
    Space -> False
    LineSeparator -> False
    ParagraphSeparator -> False
    Control -> False
    Format -> False
    Surrogate -> False
    PrivateUse -> False
    NotAssigned -> False
    _ -> True --Letter, Mark, Number, Punctuation/Quote, Symbol

--TODO maybe normal c-like identifiers, maybe identifiers that could be word-based vs. symbol-based


------ Parsing Numbers ------
--TODO common combinations of the number part parsers
anyNumber :: (Monad m, P.Stream s m Char) => ParsecT s u m Rational
anyNumber = (<?> "number") $ try $ do
    sign <- P.option 1 signLiteral
    base <- baseLiteral
    whole <- naturalLiteral base
    n <- choice [ scientificNotation whole base
                , fractionNotation whole base
                , return (whole % 1)
                ]
    return $ fromIntegral sign * n
    where
    scientificNotation whole base = do
        mantissa <- mantissaLiteral base
        (expbase, exponent) <- P.option (1,0) (decimalExp <|> hexExp)
        return $ ((whole % 1) + mantissa) * (fromIntegral expbase ^^ exponent)
    fractionNotation whole base = (whole %) . denominator <$> denominatorLiteral base
    decimalExp = (,) 10 <$> exponentLiteral 10
    hexExp = (,) 16 <$> exponentLiteral 16 



    --(<?> "number") . try $ do
    --sign <- P.option 1 signLiteral
    --base <- baseLiteral
    --whole <- naturalLiteral base
    --let scientificNotation = do
    --    mantissa <- mantissaLiteral base
    --    (expbase, exponent) <-    ((,) 10 <$> exponentLiteral 10)
    --                        P.<|> ((,) 16 <$> exponentLiteral 16)
    --    return (whole%1 + mantissa) * (expbase ^^ exponent)
        
    --number <- scientificNotation base P.<|> (whole +) <$> P.option (0%1) denominatorLiteral
    --return (sign * number)


signLiteral :: (Monad m, P.Stream s m Char) => ParsecT s u m Integer
signLiteral = (<?> "sign") $ (char '-' >> return (-1)) P.<|> (char '+' >> return 1)

baseLiteral :: (Monad m, P.Stream s m Char) => ParsecT s u m Int
baseLiteral = choice [ (stringICase "0x") >> return 16
                     , (stringICase "0o") >> return  8
                     , (stringICase "0b") >> return  2
                     ,                       return 10
                     ]

naturalLiteral :: (Monad m, P.Stream s m Char) => Int -> ParsecT s u m Integer
naturalLiteral base = (<?> "natural number") $ stringToInteger base <$> P.many1 (xDigit base)

mantissaLiteral :: (Monad m, P.Stream s m Char) => Int -> ParsecT s u m Rational
mantissaLiteral base = (<?> "mantissa") $ do
    char '.'
    stringToMantissa base <$> P.many1 (xDigit base)

exponentLiteral :: (Monad m, P.Stream s m Char) => Int -> ParsecT s u m Integer
exponentLiteral base = (<?> "exponent") (go base)
    where
    body = (*) <$> P.option 1 signLiteral <*> naturalLiteral base
    go 10 = charICase 'e' >> body
    go 16 = charICase 'h' >> body
    go _ = error "unrecognized base in Language.Parser.exponentLiteral (accepts only 10 or 16)"

denominatorLiteral :: (Monad m, P.Stream s m Char) => Int -> ParsecT s u m Rational
denominatorLiteral base = (<?> "denominator") $ do
    denom <- char '/' >> naturalLiteral base
    if denom == 0 then parserZero else return (1%denom)


xDigit :: (Monad m, P.Stream s m Char) => Int -> ParsecT s u m Char
xDigit base = case base of
    2  -> oneOf "01"
    8  -> P.octDigit
    10 -> P.digit
    16 -> P.hexDigit
    _ -> error "unrecognized base in Language.Parser.xDigit (accepts only 2, 8, 10, or 16)"

stringToInteger :: Int -> String -> Integer
stringToInteger base = foldl impl 0
    where impl acc x = acc * fromIntegral base + (fromIntegral . digitToInt) x

stringToMantissa :: Int -> String -> Ratio Integer
stringToMantissa base = (/ (fromIntegral base%1)) . foldr impl (0 % 1)
    where impl x acc = acc / (fromIntegral base%1) + (((%1) . fromIntegral . digitToInt) x)


------ Parsing Character Literals ------
literalChar :: (Monad m, P.Stream s m Char) => ParsecT s u m Char
literalChar = (satisfy isNormalChar <?> "printing character") P.<|> (escape <?> "escape sequence")
    where
    isNormalChar c = c >= ' ' && c `notElem` "\DEL\'\"\\" --FIXME limit this slightly more
    escape = char '\\' >> P.choice [specialEscape, numericalEscape]
    specialEscape = fromJust . flip lookup table <$> oneOf (map fst table)
        where table = [ ('0' , '\0')
                      , ('a' , '\a')
                      , ('b' , '\b')
                      , ('e' , '\27')
                      , ('f' , '\f')
                      , ('n' , '\n')
                      , ('r' , '\r')
                      , ('t' , '\t')
                      , ('\'', '\'')
                      , ('\"', '\"')
                      , ('\\', '\\')
                      ]
    numericalEscape = chr . fromInteger <$> P.choice [ascii16, uni4, ascii8, uni6]
    ascii8  = stringToInteger 8  <$> (oneOf "oO" >> P.count 3 P.octDigit)
    ascii16 = stringToInteger 16 <$> (oneOf "xX" >> P.count 2 P.hexDigit)
    uni4    = stringToInteger 16 <$> (char  'u'  >> P.count 4 P.hexDigit)
    uni6    =                         char   'U' >> (high P.<|> low)
        where
        low  =                 stringToInteger 16 <$> (char    '0' >> P.count 5 P.hexDigit)
        high =  (+ 0x100000) . stringToInteger 16 <$> (string "10" >> P.count 4 P.hexDigit)

maybeLiteralChar :: (Monad m, P.Stream s m Char) => ParsecT s u m (Maybe Char)
maybeLiteralChar = (const Nothing <$> (string "\&" P.<|> lineContinue)) P.<|> (Just <$> literalChar)
    where
    lineContinue = between2 (char '\\') (P.many $ oneOf " \t\n\r") --FIXME more types of whitespace could be allowed

