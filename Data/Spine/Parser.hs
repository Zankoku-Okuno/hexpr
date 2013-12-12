module Data.Spine.Parser (
      QuasiSpineParser (..)
    , Parser
    , runQSParser
    , startState
    , parseSpine
    , parseNode
    , token
    ) where

import Data.Spine

import Control.Monad
import Text.Parsec hiding (space, spaces, newline, token)
import Text.Parsec.Char hiding (space, spaces, newline)


------ Types ------
class UnQuasiSpine a => QuasiSpineParser a where
    parseAtom :: Parser (QuasiSpine a)

type Parser = Parsec String QuasiSpineState

type IndentDepth = Int
type QuasiQuoteDepth = Int
type QuasiSpineState = ([IndentDepth], Either QuasiQuoteDepth QuasiQuoteDepth)
startState :: QuasiSpineState
startState = ([0], Right 0)


------ Entry Points ------
runQSParser :: QuasiSpineParser a => SourceName -> String -> Either ParseError [Spine a]
runQSParser path input = do
    case runP parseQuasiSpine startState path input of
        Left err  -> Left err
        Right val -> Right . map unQuasiSpine $ val

parseQuasiSpine :: QuasiSpineParser a => Parser [QuasiSpine a]
parseQuasiSpine = do
    many (try blankLine)
    xs <- parseNode `sepEndBy` nextline
    many (try blankLine) >> token eof
    return xs


------ Node Parsing ------
parseSpine :: QuasiSpineParser a => Parser (QuasiSpine a)
parseSpine = choice [ parseAtom
                    , parseQuasiQuote, parseUnquote, parseSplice, parseQuote
                    , indentNode, parenNode
                    ]
    where
    indentNode = between start end (liftM QNode $ parseNode `sepBy1` nextline)
        where
        start = try (optional (char '(') >> indent)
        end = dedent
    parenNode = between start end parseNode
        where
        start = char '('
        end = token $ char ')'

parseNode :: QuasiSpineParser a => Parser (QuasiSpine a)
parseNode = liftM QNode (parseSpine `sepEndBy1` spaces1)


------ Quote Parsing ------
parseQuasiQuote :: QuasiSpineParser a => Parser (QuasiSpine a)
parseQuasiQuote = pushQuoteLevel >> char '`' >> liftM Quasiquote parseSpine

parseUnquote :: QuasiSpineParser a => Parser (QuasiSpine a)
parseUnquote = popQuoteLevel >> char ',' >> liftM Unquote parseSpine

parseSplice :: QuasiSpineParser a => Parser (QuasiSpine a)
parseSplice = popQuoteLevel >> char '~' >> liftM Splice parseSpine

parseQuote :: QuasiSpineParser a => Parser (QuasiSpine a)
parseQuote = char '\'' >> liftM Quasiquote (inQuote parseSpine)
    where
    inQuote = between disableQuasiquote enableQuasiquote


------ Indentation Parsing ------
nextline :: Parser ()
nextline = try $ do
    expectedSpaces <- peekIndentLevel
    leadingSpaces <- lineAndLeading
    if leadingSpaces == expectedSpaces
        then return ()
        else fail "expecting same indentation level"
indent :: Parser ()
indent = try $ do
    expectedSpaces <- peekIndentLevel
    leadingSpaces <- lineAndLeading
    if leadingSpaces > expectedSpaces
        then pushIndentLevel leadingSpaces
        else fail "expecting indent"
dedent :: Parser ()
dedent = try $ do
    expectedSpaces <- popIndentLevel
    leadingSpaces <- lookAhead $ try lineAndLeading
    if leadingSpaces < expectedSpaces
        then return ()
        else fail "expected dedent"
lineAndLeading :: Parser IndentDepth
lineAndLeading = token $ do
    newline
    depth <- liftM length (many $ char ' ')
    return depth



------ Query/update indent and quote depths ------
peekIndentLevel :: Parser IndentDepth
peekIndentLevel = liftM (head . fst) getState
pushIndentLevel :: IndentDepth -> Parser ()
pushIndentLevel n = do
    (oldLevel, quoteLevel) <- getState
    putState (n : oldLevel, quoteLevel)
popIndentLevel :: Parser IndentDepth
popIndentLevel = do
    (top : oldLevel, quoteLevel) <- getState
    putState (oldLevel, quoteLevel)
    return top

peekQuoteLevel :: Parser QuasiQuoteDepth
peekQuoteLevel = do
    level <- liftM snd getState
    return $ case level of { Right x -> x; Left _ -> 0 }
pushQuoteLevel :: Parser ()
pushQuoteLevel = do
    (indentLevel, oldLevel) <- getState
    case oldLevel of
        Right x -> putState (indentLevel, Right (x+1))
        Left _ -> fail "unexpected quasiquote inside quote"
popQuoteLevel :: Parser ()
popQuoteLevel = do
    (indentLevel, oldLevel) <- getState
    case oldLevel of
        Right x -> do
            when (x <= 0) $ fail "unexpected unquote outside of quasiquote"
            putState (indentLevel, Right (x-1))
        Left _ -> fail "unexpected unquote in quote"
disableQuasiquote :: Parser ()
disableQuasiquote = do
    (indentLevel, Right quoteLevel) <- getState
    putState (indentLevel, Left quoteLevel)
enableQuasiquote :: Parser ()
enableQuasiquote = do
    (indentLevel, Left quoteLevel) <- getState
    putState (indentLevel, Right quoteLevel)


------ Basic Whitespace ------
token :: Parser a -> Parser a
token = (spaces >>)
spaces :: Parser ()
spaces = skipMany space
spaces1 :: Parser ()
spaces1 = lookAhead (oneOf " \t\n\\#") >> spaces --TODO this is a hack, but it may just work: ensure that all valid start chars are included
space :: Parser ()
space = choice [ void (oneOf " \t")
               , void (char '\\' >> newline)
               , void blockComment
               , void lineComment -- must come after block comment
               ]
    where
    lineComment = char '#' >> many (noneOf "\n")
    blockComment = void $ between (try $ string "#{") (string "}#") (many blockSegment)
        where
        blockSegment = choice [ void (noneOf "#}")
                              , void $ try (char '}' >> lookAhead (noneOf "#"))
                              , blockComment
                              , void (char '#' >> noneOf "{") -- must come after block comment
                              ]

hardNewline :: Parser ()
hardNewline = void (char '\n')
blankLine :: Parser ()
blankLine = spaces >> hardNewline
newline :: Parser ()
newline = oneNewline >> skipNewlines
    where
    oneNewline = token (hardNewline <|> eof)
    isBlankLine =  (lookAhead (try blankLine) >> return True)
               <|> (eof >> return False)
               <|> (lookAhead (try $ spaces >> eof) >> return True)
               <|> return False
    skipNewlines = isBlankLine >>= \blank -> if blank then newline else return ()

a << b = do { x <- a; b; return x }
