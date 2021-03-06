{- |

Framework for parsing spines using a variant on s-expressions (see below).
The user provides an instance of `QuasispineParser a`, and is then able to use this module to parse `Spine a`.
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
      QuasispineParser (..)
    , QuasispineState
    , Parser
    
    , runSpineParser
    , runQuasispineParser
    , runComplexSpineParser

    , parseFile
    , parseNode
    , parseSpine
    , token
    , noLayout
    , gap
    ) where

import Control.Monad
import Text.Parsec hiding (space, spaces, newline, token)
import Text.Parsec.Char hiding (space, spaces, newline)

import Data.Spine


------ Types ------
class QuasispineParser a where
    parseAtom :: Parser (Quasispine a)
    parseQuote :: Parser (Quasispine a)
    parseQuasiquote :: Parser (Quasispine a)
    parseUnquote :: Parser (Quasispine a)
    parseSplice :: Parser (Quasispine a)


{-| Type synonym for parsing quasispines. -}
type Parser = Parsec String QuasispineState

type IndentDepth = Int
type QuasiQuoteDepth = Int
newtype QuasispineState = S { unState :: ([IndentDepth], Either QuasiQuoteDepth QuasiQuoteDepth) }
startState :: QuasispineState
startState = S ([0], Right 0)


------ Entry Points ------
runSpineParser :: (QuasispineParser a, UnQuasispine a, SimplifySpine a) => SourceName -> String -> Either ParseError [Spine a]
runSpineParser path input = fmap (map $ simplifySpine . unQuasispine) (runQuasispineParser path input)

runQuasispineParser :: (QuasispineParser a) => SourceName -> String -> Either ParseError [Quasispine a]
runQuasispineParser = runParser parseFile startState

runComplexSpineParser :: (QuasispineParser a, UnQuasispine a) => SourceName -> String -> Either ParseError [Spine a]
runComplexSpineParser path input = fmap (map unQuasispine) (runQuasispineParser path input)


------ Main Parsing ------
{-| Parse a string only of quasispines separated by nextlines.
    Leading and trailing whitesapce is discarded.
-}
parseFile :: QuasispineParser a => Parser [Quasispine a]
parseFile = between skipLines (skipLines >> eof) (parseNode `sepEndBy` nextline)

{-| Parse a single atom, parethesized/indented node or a (quasi)quoted/unquoted/spliced node. -}
parseSpine :: QuasispineParser a => Parser (Quasispine a)
parseSpine = choice [ parseAtom
                    , _parseQuasiquote, _parseUnquote, _parseSplice, _parseQuote
                    , indentNode, parenNode
                    ]
    where
    indentNode = between start end (liftM QBranch $ parseNode `sepBy1` nextline)
        where
        start = try (optional (char '(') >> indent)
        end = dedent
    parenNode = between start end parseNode
        where
        start = char '('
        end = token $ char ')'

{-| Parse a number of space-separated spines. -}
parseNode :: QuasispineParser a => Parser (Quasispine a)
parseNode = liftM QBranch (parseSpine `sepEndBy1` spaces)


------ Quote Parser Wrappers ------
_parseQuote :: QuasispineParser a => Parser (Quasispine a)
_parseQuote = liftM Quasiquote $ between disableQuasiquote enableQuasiquote (parseQuote <?> "quotation operator")

_parseQuasiquote :: QuasispineParser a => Parser (Quasispine a)
_parseQuasiquote = liftM Quasiquote (pushQuoteLevel >> parseQuasiquote <?> "quotation operator")

_parseUnquote :: QuasispineParser a => Parser (Quasispine a)
_parseUnquote = liftM Unquote (popQuoteLevel >> parseUnquote <?> "quotation operator")

_parseSplice :: QuasispineParser a => Parser (Quasispine a)
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
peekIndentLevel = liftM (head . fst . unState) getState
pushIndentLevel :: IndentDepth -> Parser ()
pushIndentLevel n = do
    S (oldLevel, quoteLevel) <- getState
    putState $ S (n : oldLevel, quoteLevel)
popIndentLevel :: Parser IndentDepth
popIndentLevel = do
    S (top : oldLevel, quoteLevel) <- getState
    putState $ S (oldLevel, quoteLevel)
    return top

peekQuoteLevel :: Parser QuasiQuoteDepth
peekQuoteLevel = do
    level <- liftM (snd . unState) getState
    return $ case level of { Right x -> x; Left _ -> 0 }
pushQuoteLevel :: Parser ()
pushQuoteLevel = do
    S (indentLevel, oldLevel) <- getState
    case oldLevel of
        Right x -> putState $ S (indentLevel, Right (x+1))
        Left _ -> fail "quasiquotation operator inside quote"
popQuoteLevel :: Parser ()
popQuoteLevel = do
    S (indentLevel, oldLevel) <- getState
    case oldLevel of
        Right x -> do
            when (x <= 0) $ failure
            putState $ S (indentLevel, Right (x-1))
        Left _ -> failure
    where failure = fail "unquotation operator outside of quasiquote"
disableQuasiquote :: Parser ()
disableQuasiquote = do
    S (indentLevel, Right quoteLevel) <- getState
    putState $ S (indentLevel, Left quoteLevel)
enableQuasiquote :: Parser ()
enableQuasiquote = do
    S (indentLevel, Left quoteLevel) <- getState
    putState $ S (indentLevel, Right quoteLevel)


------ Basic Whitespace ------
{-| Wrap a token parser in this to consumes inline whitespace before continuing. -}
token :: Parser a -> Parser a
token = (spaces >>)
{-| Consume whitespace, insensitive of layout (the pattern of indents/dedents and nextlines). -}
noLayout :: Parser ()
noLayout = skipMany (choice whitespaceOptions) <?> "space"
{-| Inspects the next character to determine if it is a clear token-separator.
    Such separators are whitespace, parens, hash (#), and whatever extra characters (passed to the
    combinator) are appropriate for the language at hand.
-}
gap :: String -> Parser ()
gap extraChars = nextCharIsSpace <|> eof <?> "space before next token"
    where
    nextCharIsSpace = void . lookAhead . oneOf $ (" \t\n\\#()" ++ extraChars) --TODO ensure I have all the leading chars of space included

spaces :: Parser ()
spaces = skipMany space
space :: Parser ()
space = choice (tail whitespaceOptions) <?> "space"

hardNewline :: Parser ()
hardNewline = head whitespaceOptions
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

-- this makes available all kinds of whitespace options
-- the head of the list is a hard newline, the tail is inline whitespace
whitespaceOptions = [ void (char '\n')
                    , void (oneOf " \t")
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
