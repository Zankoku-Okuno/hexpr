{- |

Framework for parsing spines using a variant on s-expressions (see below).
The user provides an instance of `QuasiSpineParser a`, and is then able to use this module to parse `Spine a`.
To this end, three node/leaf parsers and two token combinators are provided. Sticking to these high-level functions should allow a fair amount of grammatical space while keeping the grammar simple.

The grammar for normal s-expressions is `start ::= atom | '(' start+ ')'`. 
To this, we have added quotation (including quasiquotation, unquote, and splicing), but we omit it from the grammar here for clarity.
The real extension of concrete syntax is that we add the pattern `'('? indent start+ dedent`. Further, each line at the same level of indent is wrapped into a node as well.

Substituting parenthesis for indentation appropriately greatly reduces the need for parenthesis bookeeping and improves readability, without sacrificing the advantages of s-expressions.
Readers may wonder at the optional paren that may preceed an indent: when two consecutive nodes need to be introduced, a paren may be placed on its own line.

The tokenizers also handle line continuations (backslash-newline), as well as line comments (introduced with `#`) and nested block comments (surounded by `#{` and `}#`).
A comment or line continuation cound as one space for the purposes of separating tokens.

There are three entry points, which parse a quasispine and perform some amount of tidying up: convertion to a plain spline and simplify.

At the moment, comments are delimited with # and #{ ... }#.
I'd advise against allowing these patterns in atoms.
On the other hand, I may decide to parameterize these, at which point, you can mix and match to taste.
Parenthesis should probably always be kept out of user parsers.

-}

module Data.Spine.Parser (
      QuasiSpineParser (..)
    , Parser
    
    , runSpineParser
    , runQuasiSpineParser
    , runComplexSpineParser

    , parseFile
    , parseNode
    , parseSpine
    , token
    , gap
    ) where

import Control.Monad
import Text.Parsec hiding (space, spaces, newline, token)
import Text.Parsec.Char hiding (space, spaces, newline)

import Data.Spine


------ Types ------
class QuasiSpineParser a where
    parseAtom :: Parser (QuasiSpine a)
    parseQuote :: Parser (QuasiSpine a)
    parseQuasiquote :: Parser (QuasiSpine a)
    parseUnquote :: Parser (QuasiSpine a)
    parseSplice :: Parser (QuasiSpine a)


type Parser = Parsec String QuasiSpineState

type IndentDepth = Int
type QuasiQuoteDepth = Int
type QuasiSpineState = ([IndentDepth], Either QuasiQuoteDepth QuasiQuoteDepth)
startState :: QuasiSpineState
startState = ([0], Right 0)


------ Entry Points ------
runSpineParser :: (QuasiSpineParser a, UnQuasiSpine a, SimplifySpine a) => SourceName -> String -> Either ParseError [Spine a]
runSpineParser path input = fmap (map $ simplifySpine . unQuasiSpine) (runQuasiSpineParser path input)

runQuasiSpineParser :: (QuasiSpineParser a) => SourceName -> String -> Either ParseError [QuasiSpine a]
runQuasiSpineParser = runParser parseFile startState

runComplexSpineParser :: (QuasiSpineParser a, UnQuasiSpine a) => SourceName -> String -> Either ParseError [Spine a]
runComplexSpineParser path input =  fmap (map unQuasiSpine) (runQuasiSpineParser path input)


------ Main Parsing ------
parseFile :: QuasiSpineParser a => Parser [QuasiSpine a]
parseFile = between skipLines (skipLines >> eof) (parseNode `sepEndBy` nextline)

parseSpine :: QuasiSpineParser a => Parser (QuasiSpine a)
parseSpine = choice [ parseAtom
                    , _parseQuasiquote, _parseUnquote, _parseSplice, _parseQuote
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
parseNode = liftM QNode (parseSpine `sepEndBy1` spaces)


------ Quote Parser Wrappers ------
_parseQuote :: QuasiSpineParser a => Parser (QuasiSpine a)
_parseQuote = liftM Quasiquote $ between disableQuasiquote enableQuasiquote (parseQuote <?> "quotation operator")

_parseQuasiquote :: QuasiSpineParser a => Parser (QuasiSpine a)
_parseQuasiquote = liftM Quasiquote (pushQuoteLevel >> parseQuasiquote <?> "quotation operator")

_parseUnquote :: QuasiSpineParser a => Parser (QuasiSpine a)
_parseUnquote = liftM Unquote (popQuoteLevel >> parseUnquote <?> "quotation operator")

_parseSplice :: QuasiSpineParser a => Parser (QuasiSpine a)
_parseSplice = liftM Splice (popQuoteLevel >> parseSplice <?> "quotation operator")


------ Indentation Parsing ------
nextline :: Parser ()
nextline = (<?> "new line") . try $ do
    expectedSpaces <- peekIndentLevel
    leadingSpaces <- lineAndLeading
    if leadingSpaces == expectedSpaces
        then return ()
        else fail "expecting same indentation level"
indent :: Parser ()
indent = (<?> "indent") . try $ do
    expectedSpaces <- peekIndentLevel
    leadingSpaces <- lineAndLeading
    if leadingSpaces > expectedSpaces
        then pushIndentLevel leadingSpaces
        else fail "expecting indent"
dedent :: Parser ()
dedent = (<?> "dedent") . try $ do
    expectedSpaces <- popIndentLevel
    leadingSpaces <- lookAhead $ try lineAndLeading
    if leadingSpaces < expectedSpaces
        then return ()
        else fail "expected dedent"

lineAndLeading :: Parser IndentDepth
lineAndLeading = do
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
        Left _ -> fail "quasiquotation operator inside quote"
popQuoteLevel :: Parser ()
popQuoteLevel = do
    (indentLevel, oldLevel) <- getState
    case oldLevel of
        Right x -> do
            when (x <= 0) $ failure
            putState (indentLevel, Right (x-1))
        Left _ -> failure
    where failure = fail "unquotation operator outside of quasiquote"
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
gap :: String -> Parser ()
gap extraChars = nextCharIsSpace <|> eof <?> "space before next token"
    where
    nextCharIsSpace = void . lookAhead . oneOf $ (" \t\n\\#()" ++ extraChars) --TODO ensure I have all the leading chars of space included

spaces :: Parser ()
spaces = skipMany space
space :: Parser ()
space = choice [ void (oneOf " \t")
               , void (char '\\' >> newline)
               , void blockComment
               , void lineComment -- must come after block comment
               ] <?> "space"
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
skipLines :: Parser ()
skipLines = optional (try newline) --TODO not sure I need this try
newline :: Parser ()
newline = oneNewline >> skipNewlines
    where
    oneNewline = token (hardNewline <|> eof)
    isBlankLine =  (lookAhead (try $ token hardNewline) >> return True)
               <|> (eof >> return False) -- prevents infinite loop from next clause
               <|> (lookAhead (try $ spaces >> eof) >> return True)
               <|> return False
    skipNewlines = isBlankLine >>= \blank -> if blank then newline else return ()
