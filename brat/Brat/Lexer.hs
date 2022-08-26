module Brat.Lexer (Thunk(..), Tok(..), Token(..), Keyword(..), lex) where

import Prelude hiding (lex)
import Control.Exception (assert)
import Control.Monad.State (State, put, get, runState)
import Data.Char (isSpace)
import Data.Functor (($>), (<&>), void)
import Data.List (intercalate)
import Data.List.NonEmpty (nonEmpty, NonEmpty(..))
import Data.Proxy
import Data.Void
import Text.Megaparsec hiding (Token, Pos, token, State)
import Text.Megaparsec.Char

import Brat.FC
import Bwd

readL :: Read a => String -> Lexer a
readL x = case reads x of
            ((v, _):_) -> pure v
            _ -> fail ("readL failed on input " ++ x)

type Lexer a = Parsec Void String a

data Thunk where
  Kernel :: [Token] -> [Token] -> Thunk
  Lambda :: [Token] -> [Token] -> Thunk
  FunTy  :: [Token] -> [Token] -> Thunk
  -- Int: How many things does the thunk bind?
  -- The body replaces underscores with synthetic names
  Thunk  :: Int -> [Token] -> Thunk

deriving instance Eq Thunk

instance Show Thunk where
  show (Kernel ss ts) = foldMap show ss ++ show Lolly ++ foldMap show ts
  show (Lambda ss ts) = foldMap show ss ++ show FatArrow ++ foldMap show ts
  show (FunTy ss ts) = foldMap show ss ++ show Arrow ++ foldMap show ts
  show (Thunk _ toks) = foldMap show toks

data Tok
 = Ident String
 | QualifiedId (NonEmpty String) String
 | Equal
 | TypeColon
 | PortColon
 | Hole String
 | Arrow
 | FatArrow
 | Lolly
 | Curly Thunk
 | Square [Token]
 | Round [Token]
 | Semicolon
 | Comma
 | VecComma
 | K Keyword
 | DotDot
 | Number Int
 | FloatLit Double
 | Comment String
 | Newline
 | HSpace Int
 | Quoted String
 | Plus
 | Times
 | Underscore
 | UnitElem
 | LetIn [Token]
 deriving Eq

instance Show Tok where
  show (Ident s) = s
  show (QualifiedId (p :| ps) s) = intercalate "." (p:ps ++ [s])
  show Equal = "="
  show TypeColon = "::"
  show PortColon = ":"
  show (Hole h) = '?':h
  show Arrow = "->"
  show FatArrow = "=>"
  show Lolly = "-o"
  show (Curly th) = '{' : show th ++ "}"
  show (Square ts) = '[' : concatMap show ts ++ "]"
  show (Round ts) = '(' : concatMap show ts ++ ")"
  show Semicolon = ";"
  show Comma = ","
  show VecComma = ","
  show (K k) = show k
  show DotDot = ".."
  show (Number n) = show n
  show (FloatLit n) = show n
  show (Comment c) = "--" ++ c
  show Newline = "\n"
  show (HSpace n) = replicate n ' '
  show (Quoted x) = show x
  show Plus = "+"
  show Times = "*"
  show Underscore = "_"
  show UnitElem = "<>"
  show (LetIn xs) = "let" ++ (concat (show <$> xs)) ++ "in"

data Token = Token { fc :: FC
                   , _tok :: Tok
                   }
instance Eq Token where
  (Token fc t) == (Token fc' t') = t == t' && fc == fc'

instance Show Token where
  show (Token _ t) = show t
instance Ord Token where
  compare (Token (FC st nd) _) (Token (FC st' nd') _) = if st == st'
                                                        then compare nd nd'
                                                        else compare st st'

data Keyword
  = KType
  | KVec
  | KList
  | KNat
  | KInt
  | KBit
  | KBool
  | KQubit
  | KMoney
  | KPair
  | KTypeType
  | KUnit
  | KTrue | KFalse
  | KExt
  | KString
  | KOnePlus
  | KTwoTimes
  | KFloat
  | KNil
  | KCons
  | KOption
  | KSome
  | KNone
  | KImport
  deriving Eq

instance Show Keyword where
  show KType = "type"
  show KVec = "Vec"
  show KList = "List"
  show KNat = "Nat"
  show KInt = "Int"
  show KBit = "Bit"
  show KBool = "Bool"
  show KQubit = "Qubit"
  show KMoney = "Money"
  show KPair = "Pair"
  show KTypeType = "Type"
  show KUnit = "Unit"
  show KTrue = "true"
  show KFalse = "false"
  show KExt = "ext"
  show KString = "String"
  show KOnePlus = "succ"
  show KTwoTimes = "doub"
  show KFloat = "Float"
  show KNil = "nil"
  show KCons = "cons"
  show KOption = "Option"
  show KSome = "some"
  show KNone = "none"
  show KImport = "import"

keyword :: Lexer Keyword
keyword
  = ((try (string "type") $> KType)
     <|> string "Vec"   $> KVec
     <|> string "List"  $> KList
     <|> (try (string "Bool")
           <|> string "Bit") $> KBool
     <|> string "Nat"   $> KNat
     <|> string "Int"   $> KInt
     <|> string "Qubit" $> KQubit
     <|> string "Money" $> KMoney
     <|> string "Type"  $> KTypeType
     <|> string "true"  $> KTrue
     <|> string "false" $> KFalse
     <|> string "Pair"  $> KPair
     <|> string "ext"   $> KExt
     <|> try (string "String" $> KString)
     <|> string "Float" $> KFloat
     <|> try (string "nil") $> KNil
     <|> string "cons"  $> KCons
     <|> string "Option" $> KOption
     <|> string "some"  $> KSome
     <|> string "none"  $> KNone
     <|> string "Unit"  $> KUnit
     <|> string "import" $> KImport
     <|> string "succ" $> KOnePlus
     <|> string "doub" $> KTwoTimes
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

comment :: Lexer Tok
comment = string "--" *> ((printChar `manyTill` lookAhead (void newline <|> void eof)) <&> Comment)

tok :: Lexer Tok
tok = comment
      <|> try (between (char '(') (char ')') (Round <$> many token))
      <|> try (between (char '{') (char '}') (Curly <$> thunk 0 B0))
      <|> try (between (char '[') (char ']') (Square <$> many (try (en $ char ',' $> VecComma)
                                                                <|> token)))
      <|> try (Underscore <$ string "_")
      <|> try letIn
      <|> try (Quoted <$> (char '"' *> printChar `manyTill` char '"'))
      <|> try (FloatLit <$> float)
      <|> try (Number <$> number)
      <|> try (string "+" $> Plus)
      <|> try (string "*" $> Times)
      <|> try (string "->") $> Arrow
      <|> try (string "=>") $> FatArrow
      <|> try (string "-o") $> Lolly
      <|> try (Hole <$> (char '?' *> ident))
      <|> try (string "::" $> TypeColon)
      <|> try (char ':' $> PortColon)
      <|> try (char '=' $> Equal)
      <|> try (char ';' $> Semicolon)
      <|> try (char ',' $> Comma)
      <|> try (string ".." $> DotDot)
      <|> try (string "<>" $> UnitElem)
      <|> try (K <$> try keyword)
      <|> try newline'
      <|> try hspace'
      <|> try qualified
      <|> Ident <$> ident
 where
  thunk :: Int -> Bwd Token -> Lexer Thunk
  -- the n is a piece of state, but we cannot use the state monad for 'thunk' itself
  -- because we are in the parser monad. (We can for callees, however.)
  thunk n prev = try (Thunk n (prev <>> []) <$ lookAhead (string "}")) <|> do
    this <- token
    case _tok this of
      Lolly    -> assert (n == 0) $ Kernel (prev <>> []) <$> (many token)
      FatArrow -> assert (n == 0) $ Lambda (prev <>> []) <$> (many token)
      Arrow    -> assert (n == 0) $ FunTy  (prev <>> []) <$> (many token)
      _ -> let (t, n') = runState (numberUnderscoresTerm this) n in
        thunk n' (prev :< t)

  numberUnderscoresTerm :: Token -> State Int Token
  numberUnderscoresTerm t = let tk = Token (fc t) in case _tok t of
    Underscore -> do
      n <- get
      put (n+1)
      return $ tk (Ident ('\'':show n))
    Square ss -> tk . Square <$> numberUnderscoresList ss
    Round ss  -> tk . Round  <$> numberUnderscoresList ss
    LetIn ss  -> tk . LetIn  <$> numberUnderscoresList ss
    _ -> return t
  numberUnderscoresList :: [Token] -> State Int [Token]
  numberUnderscoresList = mapM numberUnderscoresTerm

  letIn = do
    string "let"
    spc <- whiteSpace
    lhs <- token `manyTill` (string "in" <* lookAhead whiteSpace)
    pure $ LetIn (spc <> lhs)

  whiteSpace :: Lexer [Token]
  whiteSpace = some (try (en hspace') <|> en newline')

  newline' :: Lexer Tok
  newline' = newline $> Newline

  hspace' :: Lexer Tok
  hspace' = do xs <- some $ satisfy $ \ x -> isSpace x && x `notElem` ['\n','\r']
               pure $ HSpace (length xs)

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
token = en tok

convPos :: SourcePos -> Pos
convPos (SourcePos _ l c) = Pos (unPos l) (unPos c)

lex :: Lexer [Token]
lex = token `manyTill` eof

tokLen :: Tok -> Int
tokLen = length . show

instance VisualStream [Token] where
  showTokens _ ts = concatMap show ts
  tokensLength _ = sum . fmap (\(Token _ t) -> tokLen t)

instance TraversableStream [Token] where
  reachOffset o pst@PosState{..} =
    let pst' = case post of
                 [] -> pstateSourcePos
                 (Token (FC (Pos l c) _) _:_) ->
                   let SourcePos file _ _ = pstateSourcePos
                   in  SourcePos file (mkPos l) (mkPos c)
        preLine = showToks . reverse . restOfLine . reverse $ pre
        prefix = (++preLine) $ if sourceLine pstateSourcePos == sourceLine pst'
                               then pstateLinePrefix
                               else []
        (pre, post) = splitStream (o - pstateOffset) pstateInput
    in (Just (prefix ++ restOfLineText post)
       , pst { pstateInput = post
             , pstateOffset = max pstateOffset o
             , pstateSourcePos = pst'
             , pstateLinePrefix = prefix
             }
       )
   where
    proxy :: Proxy [Token]
    proxy = Proxy

    restOfLine :: [Token] -> [Token]
    restOfLine = takeWhile ((/= Newline)._tok)

    showToks :: [Token] -> String
    showToks = maybe "" (showTokens proxy) . nonEmpty

    restOfLineText :: [Token] -> String
    restOfLineText = showToks . restOfLine

    splitStream :: Int -> [Token] -> ([Token], [Token])
    splitStream _ [] = ([], [])
    splitStream 0 ts = ([], ts)
    splitStream os (t:ts) = ([t], []) <> splitStream (os - 1) ts
