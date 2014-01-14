module Data.Spine.Parser (
      SpineParser
    , SpineLanguage
    , runSpineParser
    , SpineParserT
    , SpineLanguageT(..)
    , runSpineParserT

    , atom
    , separate
    , parenthesize
    , space
    , newline

    , parseSpine
    , tokenize
    , nextline
    , indent
    , dedent
    , disableIndentation
    , withQuasiquote
    , withUnquote
    , disableQuasiquotation
    ) where

import Control.Applicative ((<$>), (<*>), (<*), (*>))
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

import Text.Parsec hiding (space, newline)

import Data.Spine

------ Types and Entry ------
{-| Synonym for 'SpineLanguageT' over 'Identity'. -}
type SpineParser u a r = SpineParserT u a Identity r
{-| Type for parsers specialized to deal with spines.
    In this library, 'u' is user state, 'a' is stom type and 'r' is result type.

    In detail, we use a reader to store language configuration and a state monad
    to track indentation and quotation levels independently of user state.
    We leave this as a type synonym instead of a @newtype@ so that all the Parsec
    parsers still work.
-}
type SpineParserT u a m r = ParsecT String u (StateT InnerState (ReaderT (SpineLanguageT u m a) m)) r

data InnerState = InnerState { _indent :: Maybe [Integer], _quoteLevel :: Maybe Integer }

startInnerState :: InnerState
startInnerState = InnerState { _indent = Just [0]
                             , _quoteLevel = Just 0
                             }

{-| Synonym for 'SpineLanguageT' for parsers over 'Identity'. -}
type SpineLanguage u a = SpineLanguageT u Identity a
{-| Aggregate of parts commonly needed by a 'SpineParserT'.

-}
data SpineLanguageT u m a = SpineLanguage { _atom         :: [SpineParserT u a m a]
                                          , _separate     :: SpineParserT u a m ()
                                          , _parenthesize :: [(SpineParserT u a m (), SpineParserT u a m ())]
                                          , _space        :: SpineParserT u a m ()
                                          , _newline      :: SpineParserT u a m ()
                                          , _lineComment  :: SpineParserT u a m ()
                                          , _blockComment :: (SpineParserT u a m (), SpineParserT u a m ())
                                          , _startState   :: u
                                          }


{-| Run a spine parser in the 'Identity' monad without the fuss. -}
runSpineParser :: SpineLanguage u a -> SpineParser u a r -> SourceName -> String -> Either ParseError r
runSpineParser language parser source input = runIdentity $ runSpineParserT language parser source input

{-| Given a language configuration, perform a parse of input. -}
runSpineParserT :: (Monad m) => SpineLanguageT u m a -> SpineParserT u a m r -> SourceName -> String -> m (Either ParseError r)
runSpineParserT language parser source input = runReaderT (evalStateT parse startInnerState) language
    where
    parse = runPT parser (_startState language) source input


------ Batteries ------
{-| Parse a spine, using atom, separate and parenthesize.

    Spines are parsed as either an atom, or a `parenthesize`d node. A node, in turn, is one or more
    spines separated, and optionally terminated, by `separate`.

    In fact, this can parse any hierarchy, but the motivation is to parse spines and quasispines.
-}
parseSpine :: (Hierarchy f, Monad m) => SpineParserT u a m (f a)
parseSpine = leaf <|> branch
    where
    leaf = individual <$> atom
    branch = do
        (car:cdr) <- parenthesize (parseSpine `sepEndBy1` separate)
        return $ conjoinsl car cdr

{-| Consume \"whitespace\" characters before continuing with the passed parser.

    Whitespace means 'space', line comments (beginning with '_lineComment' and ending before 'newline'),
    and block comments (nesting between '_blockComment'). When indentation is disabled, 'newline's
    are also consumed.
-}
tokenize :: (Monad m) => SpineParserT u a m r -> SpineParserT u a m r
tokenize = (inlineSkip >>)

--TODO parse a whole file
--TODO parse a literate file (do some line-reprocessing first, then change the starting indent level to take accound of the crowsfeet)

--TODO
--parseIdentifier :: SpineParserT u a m Char -> SpineParserT u a m Char -> (Text -> Bool) -> SpineParserT u a m Text
--intLiteral :: SpineParserT u a m Integer
--floatLiteral :: SpineParserT u a m Double --FIXME should be multiple-precision
--stringLiteralChar :: SpineParserT u a m [Char]


------ Monad Access ------
{-| Parse an atom: any of the parsers supplied by '_atom'. -}
atom :: (Monad m) => SpineParserT u a m a
atom = asks _atom >>= choice

{-| Parse an atom-separator according to '_separate'. -}
separate :: (Monad m) => SpineParserT u a m ()
separate = asks _separate >>= id

{-| Perform a parse between the components of one of the elements of '_parenthesize'.

    Specifically, if @'_parenthesize' === [(a b)]@, then @parenthesize p === between a b p@.
    When multiple elements are given in '_parenthesize', the first applicable is selected.
-}
parenthesize :: (Monad m) => SpineParserT u a m r -> SpineParserT u a m r
parenthesize p = do
    parens <- asks _parenthesize
    choice [between before after p | (before, after) <- parens]

{-| Parse a non-newline space according to '_space'. -}
space :: (Monad m) => SpineParserT u a m ()
space = asks _space >>= id

{-| Parse a newline according to '_newline'. -}
newline :: (Monad m) => SpineParserT u a m ()
newline = asks _newline >>= id

{-| Parse a newline such that the next meaningful line has the same amount of leading whitespace as the previous line.
    Fails if indentation is disabled.
-}
nextline :: (Monad m) => SpineParserT u a m ()
nextline = (<?> "new line") . try $ do
    InnerState { _indent = Just (expectedSpaces:_), _quoteLevel = _ } <- get
    skipToLine
    leadingSpaces <- toInteger . length <$> many space
    if leadingSpaces == expectedSpaces
        then return ()
        else parserZero

{-| Parse an indent: next meaningful line has more leading whitespace than the previous line.
    Fails if indentation is disabled.
-}
indent :: (Monad m) => SpineParserT u a m ()
indent = (<?> "indent") . try $ do
    InnerState { _indent = Just stack@(expectedSpaces:_), _quoteLevel = ql } <- get
    skipToLine
    leadingSpaces <- toInteger . length <$> many space
    if leadingSpaces > expectedSpaces
        then put InnerState { _indent = Just (leadingSpaces:stack), _quoteLevel = ql }
        else parserZero

{-| Parse an indent: next meaningful line has less leading whitespace than the previous line.
    Fails if indentation is disabled.

    If the next line's indentation is less than the last line's, but still more than the
    previous indent, this is an error. For example, this is not accepted:

@
zero indent
    one indent
  bad indent
@
-}
dedent :: (Monad m) => SpineParserT u a m ()
dedent = (<?> "dedent") . try $ do
    InnerState { _indent = Just (_:stack@(expectedSpaces:_)), _quoteLevel = ql} <- get
    skipToLine
    leadingSpaces <- toInteger . length <$> lookAhead (many space)
    if leadingSpaces <= expectedSpaces
        then put InnerState { _indent = Just stack, _quoteLevel = ql }
        else parserZero

{-| Turns indentation off, so that 'newline' is consumed by 'tokenize' and 'indent',
    'dedent' and 'nextline' all fail.
-}
disableIndentation :: (Monad m) => SpineParserT u a m r -> SpineParserT u a m r
disableIndentation p = do
    st <- get
    between (put st { _indent = Nothing }) (put st) p

{-| Increase quasiquotation level for the passed parser. -}
withQuasiquote :: (Monad m) => SpineParserT u a m r -> SpineParserT u a m r
withQuasiquote p = do
    st@InnerState { _indent = il, _quoteLevel = Just ql } <- get
    put InnerState { _indent = il, _quoteLevel = Just (ql + 1) }
    res <- p
    put st
    return res

{-| Decrease quasiquotation level for the passed parser. Fails if quasiquotation level
    is already at zero.
-}
withUnquote :: (Monad m) => SpineParserT u a m r -> SpineParserT u a m r
withUnquote p = do
    st@InnerState { _indent = il, _quoteLevel = Just ql } <- get
    when (ql <= 0) $ fail "Unexpected unquote outside quasiquote."
    put InnerState { _indent = il, _quoteLevel = Just (ql - 1) }
    res <- p
    put st
    return res

{-| Turns quasiquotation off such that 'withQuasiquote' and 'withUnquote' both fail. -}
disableQuasiquotation :: (Monad m) => SpineParserT u a m r -> SpineParserT u a m r
disableQuasiquotation p = do
    st <- get
    between (put st { _quoteLevel = Nothing }) (put st) p


------ Helpers ------
inlineSkip :: (Monad m) => SpineParserT u a m ()
inlineSkip = do
    InnerState { _indent = depth, _quoteLevel = _ } <- get
    case depth of
        Just _  -> skipMany (space <|> lineComment <|> blockComment)
        Nothing -> skipMany (space <|> newline <|> lineComment <|> blockComment)

skipToLine :: (Monad m) => SpineParserT u a m ()
skipToLine = oneNewline >> skipBlanklines
    where
    oneNewline = tokenize (newline <|> eof)
    isBlankLine =  (lookAhead (try $ tokenize newline) >> return True)
               <|> (eof >> return False) -- prevents infinite loop from next clause
               <|> (lookAhead (try $ tokenize eof) >> return True)
               <|> return False
    skipBlanklines = isBlankLine >>= \blank -> if blank then skipToLine else return ()

lineComment :: (Monad m) => SpineParserT u a m ()
lineComment = void $ do
    asks _lineComment >>= id
    anyChar `manyTill` (lookAhead . try) newline

blockComment :: (Monad m) => SpineParserT u a m ()
blockComment = do
        (begin, end) <- asks _blockComment
        let oneBlock = void $ between (try begin) end (many blockSegment)
            blockSegment = choice [ void $ anyChar `manyTill` (lookAhead . try) end
                                  , oneBlock
                                  ]
        oneBlock
