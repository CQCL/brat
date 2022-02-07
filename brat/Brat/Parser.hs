module Brat.Parser (parseFile) where

import Brat.Error
import Brat.FC
import Brat.Lexer
import Brat.Syntax.Common hiding (K)
import Brat.Syntax.Raw

import Control.Monad (guard, void)
import Data.Bifunctor
import Data.List.NonEmpty (toList, NonEmpty(..))
import Data.Functor (($>), (<&>))
import Data.List.NonEmpty (nonEmpty)
import Data.Maybe (fromJust)
import Data.Set (empty)
import Data.Void
import Prelude hiding (lex, round)
import Text.Megaparsec hiding (Pos, Token, empty, match)

type Parser a = Parsec Void [Token] a

newline = label "\\n" $ match Newline

space :: Parser ()
space = label "whitespace" $ many (hspace <|> newline <|> (comment $> ())) $> ()

spaced :: Parser a -> Parser a
spaced p = space *> p <* space

vspace :: Parser ()
vspace = optional hspace *> many (newline <|> (comment $> ())) $> ()

hspace :: Parser ()
hspace = label "Horizontal space" $ token0 $ \case
  Token _ (HSpace _) -> Just ()
  _ -> Nothing

nextToken :: Parser Token
nextToken = lookAhead $ token0 Just

token0 x = token x empty

match :: Tok -> Parser ()
match tok = label (show tok) $ token0 $ \(Token _ t) -> if t == tok then Just () else Nothing

kmatch :: Keyword -> Parser ()
kmatch = match . K

ident :: (String -> Maybe a) -> Parser a
ident f = label "identifier" $ token0 $ \case
  (Token _ (Ident str)) -> f str
  _ -> Nothing

hole :: Parser String
hole = label "hole" $ token0 $ \case
  Token _ (Hole h) -> Just h
  _ -> Nothing

name :: Parser String
name = (<?> "name") $ token0 $ \case
  Token _ (Ident str) -> Just str
  _ -> Nothing

round :: Parser a -> Parser a
round p = label "(...)" $ token0 $ \case
  Token _ (Round toks) -> parseMaybe (spaced p) toks
  _ -> Nothing

square :: Parser a -> Parser a
square p = label "[...]" $ token0 $ \case
  Token _ (Square toks) -> parseMaybe (spaced p) toks
  _ -> Nothing

curly :: Parser a -> Parser a
curly p = label "{...}" $ token0 $ \case
  Token _ (Curly toks) -> parseMaybe (spaced p) toks
  _ -> Nothing

number :: Parser Int
number = label "nat" $ token0 $ \case
  Token _ (Number n) -> Just n
  _ -> Nothing

float :: Parser Float
float = label "float" $ token0 $ \case
  Token _ (FloatLit x) -> Just x
  _ -> Nothing

comment :: Parser Token
comment = label "Comment" $ token0 $ \case
  tok@(Token _ (Comment _)) -> Just tok
  _ -> Nothing

string :: Parser String
string = token0 $ \case
  (Token _ (Quoted txt)) -> Just txt
  _ -> Nothing

-- For the sake of ease, type aliases need to start with capital letters
typeName :: Parser String
typeName = name

port = name

comma :: Parser (WC (Raw d k) -> WC (Raw d k) -> WC (Raw d k))
comma = spaced $ token0 $ \case
  Token _ Comma -> Just $ \a b ->
    let fc = FC (start (fcOf a)) (end (fcOf b))
    in  WC fc (a ::|:: b)
  _ -> Nothing

semicolon :: Parser (WC (Raw Syn k) -> WC (Raw d Verb) -> WC (Raw d k))
semicolon = spaced $ token0 $ \case
  Token _ Semicolon -> Just $ \a b ->
    let fc = FC (start (fcOf a)) (end (fcOf b))
    in  WC fc (a ::-:: b)
  _ -> Nothing

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 px pf = px >>= rest
 where
  rhs = do f <- pf
           x <- px
           pure (f, x)

  rest x = optional rhs >>= \case
    Just (f, y) -> rest (f x y)
    Nothing     -> pure x

juxtaposition :: Parser (WC (Raw d k)) -> Parser (WC (Raw d k))
juxtaposition p = p `chainl1` (try comma)

binding :: Parser Abstractor
binding = do ps <- many (try $ portPull <* space)
             xs <- (thunk
                    <|> try (Pat <$> pat binding)
                    <|> try vecLit
                    <|> try (Lit <$> simpleTerm)
                    <|> (Bind <$> name)
                   ) `chainl1` (try portComma)
             if null ps
               then pure xs
               else pure $ APull ps xs
 where
  thunk :: Parser Abstractor
  thunk = AThunk <$> curly name

  vecLit = VecLit <$> square (binding `sepBy` (spaced (match VecComma)))

  portPull = name <* match PortColon

  portComma :: Parser (Abstractor -> Abstractor -> Abstractor)
  portComma = spaced $ token0 $ \case
    Token _ Comma -> Just (:||:)
    _ -> Nothing

pat :: Parser a -> Parser (Pattern a)
pat p = try (round onePlus)
      <|> try (round twoTimes)
      <|> try (kmatch KNil $> PNil)
      <|> try (round cons)
      <|> try (kmatch KNone $> PNone)
      <|> try (round psome)
 where
  psome = do
    kmatch KSome
    space
    PSome <$> p

  cons = do
    kmatch KCons
    space
    x <- p
    space
    xs <- p
    pure (PCons x xs)

  onePlus = do
    n <- number
    guard (n == 1)
    match Plus
    space
    POnePlus <$> p

  twoTimes = do
    n <- number
    guard (n == 2)
    match Times
    space
    PTwoTimes <$> p

sverb :: Parser (WC (Raw Syn Verb))
sverb = verbAndJuxt `chainl1` semicolon
 where
  plainVerb :: Parser (Raw Syn Verb)
  plainVerb = try func <|> try doNoun

  verbAndJuxt = withFC plainVerb `chainl1` (try comma)

  func :: Parser (Raw Syn Verb)
  func = do
    xs <- withFC binding
    spaced $ match Arrow
    body <- snoun
    pure $ xs ::\:: body

doNoun :: Parser (Raw Syn Verb)
doNoun = do
  n <- snoun
  space
  match (Round [])
  pure (RDo n)

-- not usable yet
cverb :: Parser (WC (Raw Chk Verb))
cverb = withFC $
  try (composition <?> "composition")
  <|> try (func <?> "function")
  <|> try (nhole <?> "typed hole")
  <|> (REmb <$> sverb <?> "syn verb")
 where
  nhole = RVHole <$> hole

  func :: Parser (Raw Chk Verb)
  func = do
    xs <- withFC binding <?> "bindings"
    spaced $ match Arrow
    body <- cnoun
    pure $ xs ::\:: body

  composition = compose sverb cverb

var :: Parser (Raw Syn Noun)
var = RVar <$> name

snoun :: Parser (WC (Raw Syn Noun))
snoun = (try application <|> simpleNoun) `chainl1` (try comma)
 where
--  thin :: Parser (WC (Raw Syn Noun))
--  thin = withFC $ RThin <$> (char '~' *> cnoun)

  simpleNoun :: Parser (WC (Raw Syn Noun))
  simpleNoun = withFC var

  nounAndJuxt :: Parser (WC (Raw Syn Noun))
  nounAndJuxt = round (juxtaposition snoun)
                <|> simpleNoun

  application :: Parser (WC (Raw Syn Noun))
  application = withFC $ do
    fun <- nounAndJuxt
    space
    arg <- round cnoun
    pure (fun ::$:: arg)

  nounIntoVerb :: Parser (WC (Raw Syn Noun))
  nounIntoVerb = withFC $ compose snoun sverb

  annotation = withFC $ do
    tm <- cnoun
    spaced $ match TypeColon
    ty <- outputs
    pure (tm ::::: ty)

compose :: Parser (WC (Raw Syn k)) -> Parser (WC (Raw d Verb)) -> Parser (Raw d k)
compose p1 p2 = do
  x <- p1
  spaced (match Semicolon) <?> "semicolon"
  y <- p2
  pure (x ::-:: y)

cnoun = try (withFC $ compose snoun cverb) <|> cnounWithJuxt
 where
  cnounWithJuxt :: Parser (WC (Raw Chk Noun))
  cnounWithJuxt = try (juxtaposition cnoun') <|> cnoun'

simpleTerm :: Parser SimpleTerm
simpleTerm =
  ((Text <$> string <?> "string")
  <|> try (Float <$> float <?> "float")
  <|> (Num <$> number <?> "nat")
  <|> (bool <?> "bool"))
  <|> (match UnitElem $> Unit)
 where
  bool :: Parser SimpleTerm
  bool = Bool <$> (kmatch KTrue $> True
                   <|> kmatch KFalse $> False)

cnoun' :: Parser (WC (Raw Chk Noun))
cnoun' = withFC $
  try (thunk <?> "thunk")
  <|> try (pull <?> "port pull")
  <|> try (nounIntoVerb <?> "composition")
  <|> try (pair <?> "pair")
  <|> try (selection <?> "selection")
  <|> try (vec <?> "vector literal")
  <|> (emptyVec <?> "vector literal")
  <|> (nhole <?> "hole")
  -- TODO: slice notation that isn't thunk notation
  -- <|> try (slice b <?> "slice")
  <|> try (RPattern <$> withFC (pat cnoun) <?> "pattern")
  <|> try (RSimple <$> simpleTerm)
  <|> try emb
 where
  selection :: Parser (Raw Chk Noun)
  selection = RSelect <$> snoun <*> (space *> curly cnoun')

  nhole = RNHole <$> hole

  pull = do
    ports <- some ((port <* match PortColon) <* match Comma)
    RPull ports <$> cnoun

  pair :: Parser (Raw Chk Noun)
  pair = square $ do
    left <- cnoun'
    space
    match VecComma
    space
    right <- cnoun'
    pure $ RPair left right

  emb = REmb <$> snoun

  thunk :: Parser (Raw Chk Noun)
  thunk = RTh <$> curly cverb

  nounIntoVerb :: Parser (Raw Chk Noun)
  nounIntoVerb = compose snoun cverb

  emptyVec = square $ pure $ RVec []
  vec = RVec <$> square (((:[]) <$> cnoun') `chainl1` (try (spaced (match VecComma)) $> (++)))

  -- {1,2} | {1..} | {4..5}
  -- Bool: are brackets needed?
--  slice :: Bool -> Parser (Raw Chk Noun)
--  slice True = RSlice <$> curly (try from <|> these)
--  slice False = RSlice <$> (try from <|> these)

--  these :: Parser RawSlice
--  these = These <$> (cnoun `sepBy` match Comma)

--  from :: Parser RawSlice
--  from = From <$> (cnoun <* match DotDot)

outputs :: Parser [RawIO]
outputs = ports


vtype :: Parser RawVType
vtype = vtype' []

vtype' :: [Parser RawVType] -> Parser RawVType
vtype' ps = try (round vty) <|> vty
 where
  vty = choice (try <$> ps) <|> try base <|> try alias <|> typeVar

  typeVar = RTypeFree <$> name

  base = try kernel <|> try comp <|> try vec <|> try thinning <|> simple

  alias = try aliasWithArgs <|> justAlias

  justAlias = RAlias <$> typeName <*> pure []

  kernel = curly $ do
    ss <- row
    spaced $ match Lolly
    ts <- row
    return $ RK ss ts

  aliasWithArgs = do
    alias <- typeName
    optional hspace
    args  <- (vtype' ps <* optional hspace)
             `manyTill`
             lookAhead (try (match Comma) <|> try (match Arrow) <|> try newline <|> eof)
    pure $ RAlias alias args

  comp = curly $ RC <$> ctype

  pair = do
    kmatch KPair
    hspace
    a <- vtype' ps
    hspace
    b <- vtype' ps
    pure $ RProduct a b

  vec = do
    kmatch KVec
    hspace
    ty <- vtype' ps
    hspace
    n <- cnoun
    pure $ RVector ty n

  list = do
    kmatch KList
    hspace
    RList <$> vtype' ps

  option = do
    kmatch KOption
    hspace
    ROption <$> vtype' ps

  simple = (kmatch KTypeType   $> RSimpleTy Star)
           <|> (kmatch KNat    $> RSimpleTy Natural)
           <|> (kmatch KBool   $> RSimpleTy Boolean)
           <|> (kmatch KBit    $> RSimpleTy Boolean)
           <|> (kmatch KString $> RSimpleTy TextType)
           <|> (kmatch KFloat  $> RSimpleTy FloatTy)
           <|> (kmatch KUnit   $> RSimpleTy UnitTy)
           <|> (kmatch KInt    $> RSimpleTy IntTy)
           <|> try pair
           <|> try list
           <|> try option

  thinning = do
    wee <- cnoun <?> "wee end"
    spaced $ match ThinType
    big <- cnoun <?> "big end"
    pure $ RThinning wee big

row :: Parser (Row Raw Quantum)
row = R <$> (nameAnon [0..] <$> rowElem `sepBy` void (try $ spaced comma))
 where
  nameAnon :: [Int] -> [(Maybe Port, SType Raw)] -> [(Port, SType Raw)]
  nameAnon _ [] = []
  nameAnon is ((Just p, ty):row) = (p, ty) : nameAnon is row
  nameAnon (i:is) ((Nothing, ty):row) = ('_':show i, ty) : nameAnon is row

  rowElem = try named <|> ((Nothing,) <$> stype)
  named = do
    p <- port
    spaced $ match TypeColon
    ty <- stype
    pure $ (Just p, ty)

stype :: Parser (SType Raw)
stype = try (Rho <$> square row)
        <|> try vec
        <|> match (K KQubit) $> Q Qubit
        <|> match (K KMoney) $> Q Money
        <|> match (K KBool)  $> Bit
 where
  vec :: Parser (SType Raw)
  vec = do match (K KVec)
           space
           ty <- stype
           space
           n <- cnoun
           pure $ Of ty (unWC n)


ctype :: Parser RawCType
ctype = do
  ins <- ports
  spaced $ match Arrow
  outs <- ports
  pure (ins :-> outs)

ports = (try named <|> anon) `sepBy1` try (spaced $ match Comma)
 where
  named = round $ do
    name <- port
    spaced $ match TypeColon
    Named name <$> vtype

  anon = Anon <$> vtype

withFC :: Parser a -> Parser (WC a)
withFC p = do
  (Token (FC start _) _) <- nextToken
  thing <- p
  eof <- optional eof
  case eof of
    Just _ -> pure (WC (FC start start) thing)
    Nothing -> do (Token (FC end _) _) <- nextToken
                  pure (WC (FC start end) thing)

{-
runtime :: Parser Runtime
runtime = try (char '@' *> aux <* newline) <|> pure RtLocal
 where
  aux = string "kernel" $> RtKernel
        <|> string "tk" $> RtTierkreis
-}

ndecl :: Parser RawNDecl
ndecl = do (WC fc (nm, ty, body, rt)) <- withFC $ do
             rt <- pure RtLocal -- runtime
             nm <- name
             spaced $ match TypeColon
             ty   <- outputs
             vspace
             ident $ \x -> if x == nm then Just () else Nothing
             spaced $ match Equal
             body <- cnoun
             pure (nm, ty, body, rt)
           pure $ Decl { fnName = nm
                       , fnLoc  = fc
                       , fnSig  = ty
                       , fnBody = NounBody body
                       , fnRT   = rt
                       , fnLocality = Local
                       }

vdecl :: Parser RawVDecl
vdecl = do (WC fc (nm, ty, body, rt)) <- withFC $ do
             rt   <- pure RtLocal -- runtime
             nm <- name
             spaced $ match TypeColon
             ty   <- ctype
             vspace
             body <- clauses nm
             pure (nm, ty, body, rt)
           pure $ Decl { fnName = nm
                       , fnLoc  = fc
                       , fnSig  = ty
                       , fnBody = body
                       , fnRT   = rt
                       , fnLocality = Local
                       }

parseFile = go pfile

go :: Parser a -> String -> String -> Either Error a
go p fname contents = do
  toks <- first fixLexErr (parse lex fname contents)
  first fixParseErr (parse p fname toks)
 where
  fixLexErr :: (Show e, ShowErrorComponent e)
            => ParseErrorBundle String e -> Error
  fixLexErr er = let prettyErr = errorBundlePretty er
                     -- TODO: return all of the errors
                     e :| _errs = bundleErrors er
                     fc = mkFC (errorOffset e) (bundlePosState er)
                     uglyErr = unlines . toList $ show <$> bundleErrors er
                 in  Err (Just fc) (Just fname) $ LexErr (PE uglyErr prettyErr)

  fixParseErr :: (Show e, ShowErrorComponent e)
              => ParseErrorBundle [Token] e -> Error
  fixParseErr er = let prettyErr = errorBundlePretty er
                       -- TODO: return all of the errors
                       e :| _errs = bundleErrors er
                       fc = mkFC (errorOffset e) (bundlePosState er)
                       uglyErr = unlines . toList $ show <$> bundleErrors er
                   in  Err (Just fc) (Just fname) $ ParseErr (PE uglyErr prettyErr)


  mkFC :: TraversableStream a => Int -> PosState a -> FC
  mkFC os pst = let (_, pst') = reachOffset os pst
                    SourcePos _ line col = pstateSourcePos pst'
                    l = unPos line - 1
                    c = unPos col - 1
                    start = Pos l (if c == 0 then 0 else c - 1)
                in  FC start (Pos l (c + 1))

clauses :: String -> Parser (Clause Raw Verb)
clauses declName = try noLhs <|> branches
 where
  branches = label "clauses" $ fmap (Clauses . fromJust . nonEmpty) $ some $ do
    label declName $
      ident $ \x -> if x == declName then Just () else Nothing
    space
    lhs <- (withFC binding) <?> "binding"
    spaced (match Equal)
    rhs <- cnoun
    vspace
    pure (lhs,rhs)

  noLhs = label "noLhs" $ do
    label declName $
      ident $ \x -> if x == declName then Just () else Nothing
    spaced (match Equal)
    NoLhs <$> cverb

pstmt :: Parser Env
pstmt = ((comment <?> "comment")                 <&> \_ -> ([] , [] , []))
        <|> try ((alias <?> "type alias")        <&> \x -> ([] , [] ,[x]))
        <|> try (extVDecl                        <&> \x -> ([] , [x], []))
        <|> try (extNDecl                        <&> \x -> ([x], [] , []))
        <|> try ((vdecl <?> "verb declaration")  <&> \x -> ([] , [x], []))
        <|> ((ndecl <?> "noun declaration")      <&> \x -> ([x], [] , []))
 where
  alias :: Parser (String, TypeAlias)
  alias = do (WC fc (alias, args, ty)) <- withFC aliasContents
             pure (alias, Alias fc alias args ty)


  aliasContents :: Parser (String, [String], RawVType)
  aliasContents = do
    match (K KType)
    hspace
    alias <- typeName
    optional hspace
    args  <- (name <* space) `manyTill` lookAhead (match Equal)
    spaced (match Equal)
    ty <- vtype' (mkParser <$> args)
    vspace
    let abstractTy = foldr (uncurry abstractVType) ty (zip args [0..])
    pure (alias, args, abstractTy)

  mkParser :: String -> Parser RawVType
  mkParser str = ident $ \x -> if x == str then Just (RTypeFree str) else Nothing

  extNDecl :: Parser RawNDecl
  extNDecl = do (WC fc (fnName, ty, symbol)) <- withFC $ do
                  match (K KExt)
                  space
                  symbol <- string
                  space
                  fnName <- name
                  spaced (match TypeColon)
                  ty <- outputs
                  optional hspace
                  vspace
                  pure (fnName, ty, symbol)
                pure Decl { fnName = fnName
                          , fnSig = ty
                          , fnBody = Undefined
                          , fnLoc = fc
                          , fnRT = RtLocal
                          , fnLocality = Extern symbol
                          }

  extVDecl :: Parser RawVDecl
  extVDecl = do (WC fc (fnName, ty, symbol)) <- withFC $ do
                  match (K KExt)
                  space
                  symbol <- string
                  space
                  fnName <- name
                  spaced (match TypeColon)
                  ty <- ctype
                  optional hspace
                  vspace
                  pure (fnName, ty, symbol)
                pure Decl { fnName = fnName
                          , fnSig = ty
                          , fnBody = Undefined
                          , fnLoc = fc
                          , fnRT = RtLocal
                          , fnLocality = Extern symbol
                          }

pfile :: Parser Env
pfile = space *> (foldr (<>) ([], [], []) <$> ((pstmt <* space) `manyTill` eof))
