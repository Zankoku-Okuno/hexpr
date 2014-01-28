{-# LANGUAGE FlexibleContexts #-}
{-| Convenience library for parsing 'Hexpr's, or 'Hierarchy's more generally.

    We've built this on the 'Parsec' library and kept the parsing monad implementation
    public, so all your familiar parsing functions work.

    The use case we're aiming for is:

    * Define a 'HexprLanguageT',

    * Define a top-level parser (perhaps just 'parseHexpr', or @'parseBareHexpr' \`sepEndBy\` 'nextline'@),

    * Wrap the top-level parser in 'parseFile' or 'parseLiteralFile',

    * Use 'runHexprParserT'.

-}
module Data.Hexpr.Parser (
    -- * Framework
      HexprParser
    , HexprLanguage
    , GenHexprLanguage
    , runHexprParser
    -- ** Monad Transformer
    , HexprParserT
    , HexprLanguageT(..)
    , runHexprParserT
    , InnerState
    -- ** Language Access
    , atom
    , specialNode
    , separate
    , parenthesize
    , indentize
    , space
    , newline
    -- * Batteries Included
    -- ** Parsing Whole Files
    , parseFile
    , parseLiterateFile
    -- ** Parsing Hierarchies
    , parseHexpr
    , parseBareHexpr
    , parseSexpr
    -- ** Parsing Atoms
    , parseIdentifier
    , codingChar
    , signLiteral
    , naturalLiteral
    , naturalBase
    , mantissaLiteral
    , exponentLiteral
    , stringLiteralChar
    , parseHereDoc
    , tokenize
    -- ** Languages
    , emptyLang
    -- * State Access
    -- ** Indentation
    , nextline
    , indent
    , dedent
    , disableIndentation
    , getIndentLevel
    -- ** Quasiquotation
    , withQuasiquote
    , withUnquote
    , disableQuasiquotation
    , getQuasiquoteLevel
    ) where

import Data.Maybe
import Data.List
import Data.Ratio
import Data.Char

import Control.Applicative ((<$>), (<*>), (<*), (*>))
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Text.Parsec hiding (space, newline)

import Data.Hexpr
import Data.Sexpr

------ Types and Entry ------
{-| Synonym for 'HexprLanguageT' over 'Identity'. -}
type HexprParser u h a r = HexprParserT u h a Identity r
{-| Type for parsers specialized to deal with hexpr.
    In this library, 'u' is user state, 'a' is atom type, 'h' is a hierarchy type
    to store atoms, and 'r' is result type.

    In detail, we use a reader to store language configuration and a state monad
    to track indentation and quotation levels independently of user state.
    We leave this as a type synonym instead of a @newtype@ so that all the Parsec
    parsers still work.
-}
type HexprParserT u h a m r = ParsecT String u (StateT InnerState (ReaderT (HexprLanguageT u h a m) m)) r

{-| Used to track indentation and quasiquotation state. Left opaque to minimize cross section. -}
data InnerState = InnerState { _indent :: Maybe [Integer], _quoteLevel :: Maybe Integer }

startInnerState :: InnerState
startInnerState = InnerState { _indent = Just [0]
                             , _quoteLevel = Just 0
                             }

{-| Synonym for 'GenHexprLanguage' without state -}
type HexprLanguage h a = GenHexprLanguage () h a
{-| Synonym for 'GenSpineLanguageT' for parsers over 'Identity'. -}
type GenHexprLanguage u h a = HexprLanguageT u h a Identity
{-| Aggregate of parts commonly needed by a 'HexprParserT'.

-}
data HexprLanguageT u h a m =
    HexprLanguage { _atom         :: [HexprParserT u h a m a]
                    -- ^List of parsers that recognize atoms. Each attempted in order.
                  , _specialNode  :: [HexprParserT u h a m (h a)]
                    -- ^List of parsers that recognize nodes that are neither leaves nor branches.
                  , _separate     :: HexprParserT u h a m ()
                    -- ^Separate two nodes in a branch.
                  , _indentize    :: [(HexprParserT u h a m (), HexprParserT u h a m ())]
                    -- ^Before and after parsers for recognizing indentation structures.
                  , _parenthesize :: [(HexprParserT u h a m (), HexprParserT u h a m ())]
                    -- ^Before and after parsers for recognizing parenthesized (or otherwise bracketed) structures.
                  , _space        :: HexprParserT u h a m ()
                    -- ^Whitespace that doesn't count as moving to a new line.
                  , _newline      :: HexprParserT u h a m ()
                    -- ^Whitespace that counts as moving to a new line.
                  , _lineComment  :: HexprParserT u h a m ()
                    -- ^Introduce a line comment.
                  , _blockComment :: (HexprParserT u h a m (), HexprParserT u h a m ())
                    -- ^Parsers to enclose recursive block comments.
                  , _startState   :: u
                    -- ^Starting user state.
                  }


{-| Run a hexpr parser in the 'Identity' monad without the fuss. -}
runHexprParser :: GenHexprLanguage u h a-> HexprParser u h a r -> SourceName -> String -> Either ParseError r
runHexprParser language parser source input = runIdentity $ runHexprParserT language parser source input

{-| Given a language configuration, perform a parse of input. -}
runHexprParserT :: (Monad m) => HexprLanguageT u h a m -> HexprParserT u h a m r -> SourceName -> String -> m (Either ParseError r)
runHexprParserT language parser source input = runReaderT (evalStateT parse startInnerState) language
    where
    parse = runPT parser (_startState language) source input


------ Batteries ------
{-| Parse a hexpr, using atom, separate and parenthesize/indentize.

    Hexprs are parsed as either an 'atom', or a 'parenthesize'd or 'indentize'd node. A node,
    in turn, is one or more hexpr separated, and optionally terminated, by 'separate'.

    In fact, this can parse any hierarchy, but the motivation is to parse hexpr and quasihexprs.
-}
parseHexpr :: (Hierarchy h, Monad m) => HexprParserT u h a m (h a)
parseHexpr = leaf <|> specialNode <|> indentBranch <|> parenBranch
    where
    leaf = individual <$> atom
    indentBranch = indentize parseBareHexpr >>= \(x:xs) -> return (x `adjoins` xs)
    parenBranch = parenthesize parseBareHexpr

{-| Parse a branch, with nodes separated by 'separate', but without enclosing parenthesization or
    indentization needed.
-}
parseBareHexpr :: (Hierarchy h, Monad m) => HexprParserT u h a m (h a)
parseBareHexpr = do
    (car:cdr) <- parseHexpr `sepEndBy1` separate
    return $ car `adjoins` cdr    

{-| Parse an 'Sexpr' with the same strategy as 'parseHexpr'. -}
parseSexpr :: (Monad m) => HexprParserT u h a m (Sexpr a)
parseSexpr = choice [ Atom  <$> atom
                    , Sexpr <$> parenthesize (parseSexpr `sepEndBy1` separate)
                    , Sexpr <$> indentize parseSexpr
                    ]

{-| Consume \"whitespace\" characters before continuing with the passed parser.

    Whitespace means 'space', line comments (beginning with '_lineComment' and ending before 'newline'),
    and block comments (nesting between '_blockComment'). When indentation is disabled, 'newline's
    are also consumed.
-}
tokenize :: (Monad m) => HexprParserT u h a m r -> HexprParserT u h a m r
tokenize = (inlineSkip >>)

{-| Parse a whole file, skipping to the first meaningful line and ensuring the
    next \"meaningful\" item after the passed parser completes is the end of file.

    This function really only makes sense as a top-level wrapper around the real parser.
    That is, use it only in something like
    
    @
    runSomething sourcename input = 'runHexprParserT' someLang ('parseFile' someParser) sourcename input
    @
-}
parseFile :: (Monad m) => HexprParserT u h a m r -> HexprParserT u h a m r
parseFile p = between (optional skipToLine) (optional skipToLine >> eof) p

{-| Parse a file after preprocessing the stream so that literate files are accepted.
    Specifically, given a string @s@, throw away any line that does not begin with @s@
    and strip @s@ from the lines that do start with @s@. This preprocessing preserves
    position reporting.

    WARNING: This combinator initializes the parser state, so don't use
    it except as a top-level wrapper. As 'parseFile', it also doesn't make sense
    outside that context.
-}
parseLiterateFile :: (Monad m) => String -> HexprParserT u h a m r -> HexprParserT u h a m r
parseLiterateFile leader p = do
        setInput =<< preprocess <$> getInput
        put InnerState { _indent = Just [fromIntegral leadingSpaces], _quoteLevel = Just 0 }
        parseFile p
    where
    preprocess = unlines . map doline . lines
    doline s | leader `isPrefixOf` s = cleanedLine s
             | otherwise = ""
    cleanedLine s = replicate leadingSpaces ' ' ++ drop leadingSpaces s
    leadingSpaces = length leader


{-| Given two 'Char' parsers, parse one character of the first, and many characters
    of the second.
-}
parseIdentifier :: (Monad m) => HexprParserT u h a m Char -> HexprParserT u h a m Char -> HexprParserT u h a m String
parseIdentifier p1 pRest = do
    x <- p1
    xs <- many pRest
    return (x:xs)

{-| Accept unicode characters that could reasonably be used in a source code identifier.
    It rejects any space characters, separators, control/format characters as well as private
    use and unassigned characters. Pass a predicate function in to exclude further characters.
    All other unicode characters are accepterd: letters, marks, punctuation and symbols.
-}
codingChar :: (Monad m, Stream s m Char) => (Char -> Bool ) -> ParsecT s u m Char
codingChar p = satisfy $ \c -> isCodingChar c && not (p c)
    where
    isCodingChar c = case generalCategory c of
        Space -> False
        LineSeparator -> False
        ParagraphSeparator -> False
        Control -> False
        Format -> False
        Surrogate -> False
        PrivateUse -> False
        NotAssigned -> False
        _ -> True --Letter, Mark, Number, Punctuation/Quote, Symbol


{-| Parse arithmentic sign, default positive, using @\/[+-]?\/@ -}
signLiteral :: (Monad m) => HexprParserT u h a m Integer
signLiteral = option 1 $ (char '-' >> return (-1)) <|> (char '+' >> return 1)

{-| Parse an integer literal of the form @\/0x[0-9a-fA-F]+|0o[0-7]+|0b[01]+|[0-9]+\/@.
    The integer parse is the first of the returned pair. The second is the base.

    The unary operators negate and positive are not parsed, since they may depend
    on the language in question.
-}
naturalLiteral :: (Monad m) => HexprParserT u h a m (Integer, Integer)
naturalLiteral = choice [ baseInt 16 "xX" hexDigit
                        , baseInt 8  "xX" octDigit
                        , baseInt 2  "bB" (oneOf "01")
                        , decInt
                        ]
    where
    decInt = do
        n <- stringToInteger 10 <$> many1 digit
        return (n, 10)
    baseInt base sigils digit = do
        try $ char '0' >> oneOf sigils
        n <- stringToInteger base <$> many1 digit
        return (n, base)

{-| Parse a natural number given a base (2, 8, 10 or 16). 

    Neither sign nor prefix are parsed, just the digits.
-}
naturalBase :: (Monad m) => Integer -> HexprParserT u h a m Integer
naturalBase  2 = stringToInteger  2 <$> many1 (oneOf "01")
naturalBase  8 = stringToInteger 8  <$> many1 octDigit
naturalBase 10 = stringToInteger 10 <$> many1 digit
naturalBase 16 = stringToInteger 16 <$> many1 hexDigit
naturalBase _ = error "naturalBase: unrecognized base (expecting 2, 8, 10 or 16)"

{-| Parse the second half of a point literal with the form @\/\\.[0-9]+\/@.
    The form above is for a decimal base; alternate bases can also be passed in.
    The bases 2, 8, 10 and 16 are understood.

    As with 'naturalLiteral', the unary operators negate and positive are not parsed.
    Further, @+inf@, @-inf@ and @NaN@ are not parsed.
-}
mantissaLiteral :: (Monad m) => Integer -> HexprParserT u h a m Rational
mantissaLiteral base = do
    char '.'
    stringToMantissa base <$> many1 xDigit
    where
    xDigit = case base of
        2  -> oneOf "01"
        8  -> octDigit
        10 -> digit
        16 -> hexDigit
        _ -> error "unrecognized base in Data.Hexpr.Parser.mantissaLiteral"

{-| Parse the exponent of a floating point literal with the form 
    @\/([eE][+-]?[0-9]+|[hH][+-]?[0-9a-fA-F]+)?\/@
-}
exponentLiteral :: (Monad m) => HexprParserT u h a m Rational
exponentLiteral = option 1 (decimalExp <|> hexExp)
    where
    decimalExp = do
        oneOf "eE"
        sign <- signLiteral
        e <- stringToInteger 10 <$> many1 digit
        return $ 10 ^^ (sign * e)
    hexExp = do
        oneOf "hH"
        sign <- option 1 $ (char '-' >> return (-1)) <|> (char '+' >> return 1)
        e <- stringToInteger 16 <$> many1 hexDigit
        return $ 16 ^^ (sign * e)


{-| Parse a single (meaningful) character or else an empty character. This should be applicable
    to both character and string literals. For character literals, use this function directly,
    and extract from the 'Just'. For string literals, use @'catMaybes' \<$\> 'many' 'stringLiteralChar'@.

    Here's the list of what characters are accepted:

    * Any single unicode character that is not an ASCII control character, backslash, or double-quote.

    * Line continuation: backslash, then advance over whitespace
        (including newlines and comments) through the next backslash.

    * Octal or hexadecimal ASCII escapes: a sequence in @\/\\\\(x[0-9a-fA-F]{2}|o[0-7]{3})\/@.

    * Unicode escapes: a sequence in @\/\\\\(u|U0[0-9a-fA-F]|U10)[0-9a-fA-F]{4}\/@.

    * Special escape: a sequence in @\/\\\\[0abefnrtv\'\"&]\/@.
        For reference, the meanings of special escapes are:
    
@
\\0: nul             (ASCII 0,  0x00)
\\a: bell            (ASCII 7,  0x07)
\\b: backspace       (ASCII 8,  0x08)
\\e: escape          (ASCII 27, 0x1B)
\\f: form feed       (ASCII 12, 0x0C)
\\n: line feed       (ASCII 10, 0x0A)
\\r: carriage return (ASCII 13, 0x0D)
\\t: horizontal tab  (ASCII 9,  0x09)
\\v: vertical tab    (ASCII 11, 0x0B)
\\\': single quote    (ASCII 39, 0x27)
\\\": double quote    (ASCII 34, 0x22)
\\&: empty string
@
-}
stringLiteralChar :: (Monad m) => HexprParserT u h a m (Maybe Char)
stringLiteralChar = normalChar <|> try escape
    where
    normalChar = Just <$> satisfy (\c -> c >= ' ' && c `notElem` "\DEL\"\\")
    escape = char '\\' >> choice [specialEscape, numericalEscape, lineContinue]
    specialEscape = fromJust . flip lookup table <$> oneOf (map fst table)
        where table = [ ('0' , Just '\0')
                      , ('a' , Just '\a')
                      , ('b' , Just '\b')
                      , ('e' , Just '\27')
                      , ('f' , Just '\f')
                      , ('n' , Just '\n')
                      , ('r' , Just '\r')
                      , ('t' , Just '\t')
                      , ('\'', Just '\'')
                      , ('\"', Just '\"')
                      , ('\\', Just '\\')
                      , ('&' , Nothing)
                      ]
    numericalEscape = Just . chr . fromInteger <$> choice [ascii16, uni4, ascii8, uni6]
    ascii8  = stringToInteger 8  <$> (oneOf "oO" >> count 3 octDigit)
    ascii16 = stringToInteger 16 <$> (oneOf "xX" >> count 2 hexDigit)
    uni4    = stringToInteger 16 <$> (char  'u'  >> count 4 hexDigit)
    uni6    =                         char   'U' >> (high <|> low)
        where
        low  =                 stringToInteger 16 <$> (char    '0' >> count 5 hexDigit)
        high =  (+ 0x100000) . stringToInteger 16 <$> (string "10" >> count 4 hexDigit)
    lineContinue = disableIndentation (tokenize $ char '\\') >> return Nothing

{-| Parse a heredoc introduced by the passed prefix string. Heredocs are strings
    which continue until some specified (per-heredoc) terminator appears on its own line.
    With heredocs, you can write string literals without escapes simply by choosing an
    appropriate terminator.

    For example, if the prefix were @\"\>\>\>\"@, the following is two heredocs (one after the other):

@
\>\>\>end
some regex:
    \[^\n]*
end
\>\>\>FOO
end
FOO
@
    
    Specifically, we match the prefix, then extract any number of chars (possibly empty) up
    to the first newline (actual @\'\\n\'@) to use as the terminator. The content begins on
    the next line, and continues up to the first line where the terminator appears on its own.
    The terminator line is consumed, but is not part of the content. All characters found in
    the body are passed through unadulterated.
-}
parseHereDoc :: (Monad m) => String -> HexprParserT u h a m String
parseHereDoc prefix = do
    try (string prefix)
    terminate <- anyChar `manyTill` (char '\n')
    let terminalLine = string $ if terminate == "\n" then "\n" else ('\n':terminate)
    anyChar `manyTill` try terminalLine


------ Default Languages ------
emptyLang :: (Monad m) => u -> HexprLanguageT u h a m
emptyLang start = HexprLanguage { _atom = []
                                , _specialNode = []
                                , _separate = do
                                                lookAhead $ oneOf " ()#\n\t"
                                                tokenize $ return ()
                                , _indentize = [(indent, dedent)]
                                , _parenthesize = [(void $ char '(', void $ char ')')]
                                , _space = void (oneOf " \t") <|> try (void $ string "\\\n")
                                , _newline = void $ char '\n'
                                , _lineComment = parserZero
                                , _blockComment = (parserZero, parserZero)
                                , _startState = start
                                }

------ Monad Access ------
{-| Parse an atom: any of the parsers supplied by '_atom'. -}
atom :: (Monad m) => HexprParserT u h a m a
atom = asks _atom >>= choice

{-| Parse a node of a hierarchy that is neither a leaf nor branch. -}
specialNode :: (Hierarchy h, Monad m) => HexprParserT u h a m (h a)
specialNode = asks _specialNode >>= choice

{-| Parse an atom-separator according to '_separate'. -}
separate :: (Monad m) => HexprParserT u h a m ()
separate = asks _separate >>= id

{-| Parse many, each on its own line, and wrapped in one of the '_indentize' parsers. -}
indentize :: (Monad m) => HexprParserT u h a m r -> HexprParserT u h a m [r]
indentize p = do
    dents <- asks _indentize
    choice [between before after (p `sepBy1` nextline) | (before, after) <- dents]

{-| Perform a parse between the components of one of the elements of '_parenthesize'.

    Specifically, if @'_parenthesize' === [(a b)]@, then @parenthesize p === between a b p@.
    When multiple elements are given in '_parenthesize', the first applicable is selected.
-}
parenthesize :: (Monad m) => HexprParserT u h a m r -> HexprParserT u h a m r
parenthesize p = do
    parens <- asks _parenthesize
    choice [between before after p | (before, after) <- parens]

{-| Parse a non-newline space according to '_space'. -}
space :: (Monad m) => HexprParserT u h a m ()
space = asks _space >>= id

{-| Parse a newline according to '_newline'. -}
newline :: (Monad m) => HexprParserT u h a m ()
newline = asks _newline >>= id

{-| Parse a newline such that the next meaningful line has the same amount of leading whitespace as the previous line.
    Fails if indentation is disabled.
-}
nextline :: (Monad m) => HexprParserT u h a m ()
nextline = (<?> "new line") . try $ do
    InnerState { _indent = Just (expectedSpaces:_), _quoteLevel = _ } <- get
    skipToLine
    leadingSpaces <- toInteger . length <$> many (char ' ')
    if leadingSpaces == expectedSpaces
        then return ()
        else parserZero

{-| Parse an indent: next meaningful line has more leading whitespace than the previous line.
    Fails if indentation is disabled.
-}
indent :: (Monad m) => HexprParserT u h a m ()
indent = (<?> "indent") . try $ do
    InnerState { _indent = Just stack@(expectedSpaces:_), _quoteLevel = ql } <- get
    skipToLine
    leadingSpaces <- toInteger . length <$> many (char ' ')
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
dedent :: (Monad m) => HexprParserT u h a m ()
dedent = (<?> "dedent") . try $ do
    InnerState { _indent = Just (_:stack@(expectedSpaces:_)), _quoteLevel = ql} <- get
    skipToLine
    leadingSpaces <- toInteger . length <$> lookAhead (many (char ' '))
    if leadingSpaces <= expectedSpaces
        then put InnerState { _indent = Just stack, _quoteLevel = ql }
        else parserZero

{-| Turns indentation off, so that 'newline' is consumed by 'tokenize' and 'indent',
    'dedent' and 'nextline' all fail.
-}
disableIndentation :: (Monad m) => HexprParserT u h a m r -> HexprParserT u h a m r
disableIndentation p = do
    st <- get
    between (put st { _indent = Nothing }) (put st) p

{-| Increase quasiquotation level for the passed parser. -}
withQuasiquote :: (Monad m) => HexprParserT u h a m r -> HexprParserT u h a m r
withQuasiquote p = do
    st@InnerState { _indent = il, _quoteLevel = Just ql } <- get
    put InnerState { _indent = il, _quoteLevel = Just (ql + 1) }
    res <- p
    put st
    return res

{-| Current number of leading spaces. Fails if indentation is disabled. -}
getIndentLevel :: (Monad m) => HexprParserT u h a m Integer
getIndentLevel = (\InnerState { _indent = Just (x:_), _quoteLevel = _} -> x) <$> get


{-| Decrease quasiquotation level for the passed parser. Fails if quasiquotation level
    is already at zero.
-}
withUnquote :: (Monad m) => HexprParserT u h a m r -> HexprParserT u h a m r
withUnquote p = do
    st@InnerState { _indent = il, _quoteLevel = Just ql } <- get
    when (ql <= 0) $ fail "Unexpected unquote outside quasiquote."
    put InnerState { _indent = il, _quoteLevel = Just (ql - 1) }
    res <- p
    put st
    return res

{-| Turns quasiquotation off such that 'withQuasiquote' and 'withUnquote' both fail. -}
disableQuasiquotation :: (Monad m) => HexprParserT u h a m r -> HexprParserT u h a m r
disableQuasiquotation p = do
    st <- get
    between (put st { _quoteLevel = Nothing }) (put st) p

{-| Current number of enclosing quasiquotes minus enclosing unquotes.
    Fails if quasiquotation is disabled.
-}
getQuasiquoteLevel :: (Monad m) => HexprParserT u h a m Integer
getQuasiquoteLevel = (\InnerState { _indent = _, _quoteLevel = Just x} -> x) <$> get


------ Helpers ------
inlineSkip :: (Monad m) => HexprParserT u h a m ()
inlineSkip = do
    InnerState { _indent = depth, _quoteLevel = _ } <- get
    case depth of
        Just _  -> skipMany (space <|> lineComment <|> blockComment)
        Nothing -> skipMany (space <|> newline <|> lineComment <|> blockComment)

skipToLine :: (Monad m) => HexprParserT u h a m ()
skipToLine = oneNewline >> skipBlanklines
    where
    oneNewline = tokenize (newline <|> eof)
    isBlankLine =  (lookAhead (try $ tokenize newline) >> return True)
               <|> (eof >> return False) -- prevents infinite loop from next clause
               <|> (lookAhead (try $ tokenize eof) >> return True)
               <|> return False
    skipBlanklines = isBlankLine >>= \blank -> if blank then skipToLine else return ()

lineComment :: (Monad m) => HexprParserT u h a m ()
lineComment = void $ do
    asks _lineComment >>= id
    anyChar `manyTill` lookAhead (try newline <|> eof)

blockComment :: (Monad m) => HexprParserT u h a m ()
blockComment = do
        (begin, end) <- asks _blockComment
        let oneBlock = void $ begin >> inBlock `manyTill` end
            inBlock = oneBlock <|> void anyChar
        oneBlock

stringToInteger :: Integer -> String -> Integer
stringToInteger base = foldl impl 0
    where impl acc x = acc * base + (fromIntegral . digitToInt) x

stringToMantissa :: Integer -> String -> Ratio Integer
stringToMantissa base = (/ (base%1)) . foldr impl (0 % 1)
    where impl x acc = acc / (base%1) + (((%1) . fromIntegral . digitToInt) x)
