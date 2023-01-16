module Brat.Lexer (Tok(..), Token(..), Keyword(..), lex) where

import Prelude hiding (lex)
import Data.Char (isSpace)
import Data.Functor (($>), void)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Void
import Text.Megaparsec hiding (Token, Pos, token, State, between)
import Text.Megaparsec.Char hiding (space)

import Brat.FC

readL :: Read a => String -> Lexer a
readL x = case reads x of
            ((v, _):_) -> pure v
            _ -> fail ("readL failed on input " ++ x)

type Lexer a = Parsec Void String a

data Tok
 = Ident String
 | QualifiedId (NonEmpty String) String
 | Equal
 | KindColon
 | TypeColon
 | PortColon
 | Hole String
 | Arrow
 | FatArrow
 | Lolly
 | LParen
 | RParen
 | LBrace
 | RBrace
 | LBracket
 | RBracket
 | Semicolon
 | Into
 | Comma
 | K Keyword
 | DotDot
 | Number Int
 | FloatLit Double
 | Comment String
 | Newline
 | Quoted String
 | Plus
 | Asterisk
 | Hash
 | Underscore
 deriving Eq

instance Show Tok where
  show (Ident s) = s
  show (QualifiedId (p :| ps) s) = intercalate "." (p:ps ++ [s])
  show Equal = "="
  show KindColon = "<-"
  show TypeColon = "::"
  show PortColon = ":"
  show (Hole h) = '?':h
  show Arrow = "->"
  show FatArrow = "=>"
  show Lolly = "-o"
  show LParen = "("
  show RParen = ")"
  show LBrace = "{"
  show RBrace = "}"
  show LBracket = "["
  show RBracket = "]"
  show Semicolon = ";"
  show Into = "|>"
  show Comma = ","
  show (K k) = show k
  show DotDot = ".."
  show (Number n) = show n
  show (FloatLit n) = show n
  show (Comment c) = "--" ++ c
  show Newline = "\n"
  show (Quoted x) = show x
  show Plus = "+"
  show Asterisk = "*"
  show Hash = "#"
  show Underscore = "_"

data Token = Token { fc :: FC
                   , _tok :: Tok
                   }
instance Eq Token where
  (Token fc t) == (Token fc' t') = t == t' && fc == fc'

instance Show Token where
  show (Token _ t) = (show t) ++ " "
instance Ord Token where
  compare (Token (FC st nd) _) (Token (FC st' nd') _) = if st == st'
                                                        then compare nd nd'
                                                        else compare st st'

data Keyword
  = KType
  | KBit
  | KBool
  | KQubit
  | KMoney
  | KExt
  | KImport
  | KLet
  | KIn
  deriving Eq

instance Show Keyword where
  show KType = "type"
  show KBit = "Bit"
  show KBool = "Bool"
  show KQubit = "Qubit"
  show KMoney = "Money"
  show KExt = "ext"
  show KImport = "import"
  show KLet = "let"
  show KIn = "in"

keyword :: Lexer Keyword
keyword
  = ((try (string "type") $> KType)
     <|> (try (string "Bool")
           <|> string "Bit") $> KBool
     <|> string "Qubit" $> KQubit
     <|> string "Money" $> KMoney
     <|> string "ext"   $> KExt
     <|> string "import" $> KImport
     <|> string "let" $> KLet
     <|> string "in" $> KIn
    ) <* notFollowedBy identChar

identChar :: Lexer Char
identChar = alphaNumChar <|> oneOf "_'"

ident :: Lexer String
ident = (<?> "name") $ do
  a <- letterChar
  bc <- many identChar
  pure (a:bc)

qualified :: Lexer Tok
qualified = (<?> "qualified name") $ do
  first <- ident <* string "."
  rest  <- many (try $ ident <* string ".")
  last  <- ident
  pure (QualifiedId (first :| rest) last)

space :: Lexer ()
space = (many $ (satisfy isSpace >> return ()) <|> comment) >> return ()
 where
  comment :: Lexer ()
  comment = string "--" *> ((printChar `manyTill` lookAhead (void newline <|> void eof)) >> return ())

tok :: Lexer Tok
tok = (   try (char '(' $> LParen)
      <|> try (char ')' $> RParen)
      <|> try (char '{' $> LBrace)
      <|> try (char '}' $> RBrace)
      <|> try (char '[' $> LBracket)
      <|> try (char ']' $> RBracket)
      <|> try (Underscore <$ string "_")
      <|> try (Quoted <$> (char '"' *> printChar `manyTill` char '"'))
      <|> try (FloatLit <$> float)
      <|> try (Number <$> number)
      <|> try (string "+" $> Plus)
      <|> try (string "->") $> Arrow
      <|> try (string "=>") $> FatArrow
      <|> try (string "-o") $> Lolly
      <|> try (Hole <$> (char '?' *> ident))
      <|> try (string "::" $> TypeColon)
      <|> try (char ':' $> PortColon)
      <|> try (char '=' $> Equal)
      <|> try (char ';' $> Semicolon)
      <|> try (string "|>" $> Into)
      <|> try (char ',' $> Comma)
      <|> try (string ".." $> DotDot)
      <|> try (string "<-" $> KindColon)
      <|> try (string "#"  $> Hash)
      <|> try (string "*"  $> Asterisk)
      <|> try (K <$> try keyword)
      <|> try qualified
      <|> Ident <$> ident
      )
 where
  float :: Lexer Double
  float = label "float literal" $ do
    msign <- optional (char '-')
    n <- some digitChar
    char '.'
    m <- some digitChar
    let val = n ++ "." ++ m
    readL (maybe val (:val) msign)

  number :: Lexer Int
  number = label "number literal" $ do
    msign <- optional (char '-')
    val <- some digitChar
    readL (maybe val (:val) msign)

en :: Lexer Tok -> Lexer Token
en l = do st <- convPos <$> getSourcePos
          x <- l
          nd <- convPos <$> getSourcePos
          pure $ Token (FC st nd) x

token :: Lexer Token
token = space >> en tok

convPos :: SourcePos -> Pos
convPos (SourcePos _ l c) = Pos (unPos l) (unPos c)

lex :: Lexer [Token]
lex = token `manyTill` (try $ space >> eof)

tokLen :: Tok -> Int
tokLen = length . show

instance VisualStream [Token] where
  showTokens _ ts = concatMap show ts
  tokensLength _ = sum . fmap (\(Token _ t) -> tokLen t)
