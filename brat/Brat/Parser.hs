module Brat.Parser (parseFile) where

import Brat.Error
import Brat.FC
import Brat.Lexer
import Brat.Syntax.Common hiding (K)
import Brat.Syntax.Raw
import Brat.UserName

import Control.Monad (guard, void)
import Data.Bifunctor
import Data.List.NonEmpty (toList, NonEmpty(..), nonEmpty)
import Data.Functor (($>), (<&>))
import Data.Maybe (fromJust, fromMaybe)
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
vspace = many (optional hspace *> (newline <|> (comment $> ()))) $> ()

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

simpleName :: Parser String
simpleName = token0 $ \case
  Token _ (Ident str) -> Just str
  _ -> Nothing

qualifiedName :: Parser UserName
qualifiedName = (<?> "qualified name") . token0 $ \case
  Token _ (QualifiedId prefix str) -> Just (PrefixName (toList prefix) str)
  _ -> Nothing

userName :: Parser UserName
userName = (<?> "name") $ try qualifiedName <|> (PrefixName [] <$> simpleName)

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

inLet :: Parser a -> Parser a
inLet p = label "let ... in" $ token0 $ \case
  Token _ (LetIn toks) -> parseMaybe (spaced p) toks
  _ -> Nothing

number :: Parser Int
number = label "nat" $ token0 $ \case
  Token _ (Number n) -> Just n
  _ -> Nothing

float :: Parser Double
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

port = simpleName

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
             xs <- (try (Pat <$> pat binding)
                    <|> try vecLit
                    <|> try (Lit <$> simpleTerm)
                    <|> (Bind <$> simpleName)
                   ) `chainl1` (try portComma)
             if null ps
               then pure xs
               else pure $ APull ps xs
 where
  vecLit = VecLit <$> square (binding `sepBy` (spaced (match VecComma)))

  portPull = simpleName <* match PortColon

  portComma :: Parser (Abstractor -> Abstractor -> Abstractor)
  portComma = spaced $ token0 $ \case
    Token _ Comma -> Just (:||:)
    _ -> Nothing

pat :: Parser a -> Parser (Pattern a)
pat p = try onePlus
      <|> try twoTimes
      <|> try (kmatch KNil $> PNil)
      <|> try cons
      <|> try (kmatch KNone $> PNone)
      <|> try psome
 where
  psome = do
    kmatch KSome
    space
    PSome <$> round p

  cons = do
    kmatch KCons
    space
    PCons <$> round p

  onePlus = do
    kmatch KOnePlus
    space
    POnePlus <$> round p

  twoTimes = do
    kmatch KTwoTimes
    space
    PTwoTimes <$> round p

sverb :: Parser (WC (Raw Syn Verb))
sverb = verbAndJuxt `chainl1` semicolon
 where
  plainVerb :: Parser (Raw Syn Verb)
  plainVerb = try (func snoun)

  verbAndJuxt = (try (letin sverb) <|> withFC plainVerb) `chainl1` (try comma)

func :: Parser (WC (Raw d Noun)) -> Parser (Raw d Verb)
func pbody = do
  xs <- withFC binding <?> "Binding(s)"
  spaced $ match FatArrow
  body <- pbody
  pure $ xs ::\:: body

letin :: Parser (WC (Raw d k)) -> Parser (WC (Raw d k))
letin p = withFC $ do
  (lhs,rhs) <- inLet $ do
    abs <- withFC binding
    spaced $ match Equal
    thing <- snoun
    pure (abs, thing)
  space
  body <- p
  pure $ RLet lhs rhs body

-- not usable yet
cverb :: Parser (WC (Raw Chk Verb))
cverb = try (letin cverb <?> "let binding") <|> withFC
  (try (composition <?> "composition")
  <|> try (func cnoun <?> "function")
  <|> try (nhole <?> "typed hole")
  <|> (REmb <$> sverb <?> "syn verb")
  )
 where
  nhole = RVHole <$> hole

  composition = compose sverb cverb

var :: Parser (Raw Syn Noun)
var = RVar <$> userName

snoun' :: Parser (WC (Raw Syn Noun))
snoun' = try application <|> simpleNoun
 where
--  thin :: Parser (WC (Raw Syn Noun))
--  thin = withFC $ RThin <$> (char '~' *> cnoun)

  simpleNoun :: Parser (WC (Raw Syn Noun))
  simpleNoun = try (letin snoun) <|> withFC var

  nounAndJuxt :: Parser (WC (Raw Syn Noun))
  nounAndJuxt = round (juxtaposition snoun)
                <|> simpleNoun

  application :: Parser (WC (Raw Syn Noun))
  application = withFC $ do
    fun <- nounAndJuxt
    space
    arg <- round cnoun
    pure (fun ::$:: arg)

snoun :: Parser (WC (Raw Syn Noun))
snoun = snoun' `chainl1` (try comma)

compose :: Parser (WC (Raw Syn k)) -> Parser (WC (Raw d Verb)) -> Parser (Raw d k)
compose p1 p2 = do
  x <- p1
  spaced (match Semicolon) <?> "semicolon"
  y <- p2
  pure (x ::-:: y)

cnoun :: Parser (WC (Raw Chk Noun))
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
cnoun' = try (letin cnoun) <|> withFC
  (try (thunk <?> "thunk")
  <|> try (pull <?> "port pull")
  <|> try (nounIntoVerb <?> "composition")
  <|> try (selection <?> "selection")
  <|> try (vec <?> "vector literal")
  <|> (emptyVec <?> "vector literal")
  <|> (nhole <?> "hole")
  -- TODO: slice notation that isn't thunk notation
  -- <|> try (slice b <?> "slice")
  <|> try (RPattern <$> withFC (pat cnoun) <?> "pattern")
  <|> try (RSimple <$> simpleTerm)
  <|> try emb
  )
 where
  selection :: Parser (Raw Chk Noun)
  selection = RSelect <$> snoun <*> (space *> curly cnoun')

  nhole = RNHole <$> hole

  pull = do
    ports <- some (try (port <* match PortColon))
    RPull ports <$> cnoun

  emb = REmb <$> snoun'

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
outputs = rawIO vtype


vtype :: Parser RawVType
vtype = vtype' []

vtype' :: [Parser RawVType] -> Parser RawVType
vtype' ps = try (round vty) <|> vty
 where
  vty = choice (try <$> ps) <|> try base <|> try alias <|> typeVar

  typeVar = RTypeFree <$> userName

  base = try comp <|> try vec <|> try thinning <|> simple

  alias = try aliasWithArgs <|> justAlias

  justAlias = RAlias <$> userName <*> pure []

  aliasWithArgs = do
    alias <- userName
    space
    args <- round $ vtype' ps `sepBy` comma
    pure $ RAlias alias args

  comp = curly $ thunkTy

  pair = kmatch KPair *> space *> round (RProduct <$> vtype' ps <* spaced comma <*> vtype' ps)

  vec = kmatch KVec *> space *> round (RVector <$> vtype' ps <* spaced comma <*> cnoun)

  list = kmatch KList *> space *> round (RList <$> vtype' ps)

  option = kmatch KOption *> space *> round (ROption <$> vtype' ps)

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

rawIO :: Parser ty -> Parser [RawIO' ty]
rawIO tyP = rowElem `sepBy` void (try $ spaced comma)
 where
  rowElem = try (round rowElem') <|> rowElem'
  rowElem' = try named <|> (Anon <$> tyP)

  named = do
    p <- port
    spaced $ match TypeColon
    ty <- tyP
    pure $ (Named p ty)

stype :: Parser (SType' Raw)
stype = try (Rho <$> round row)
        <|> try vec
        <|> match (K KQubit) $> Q Qubit
        <|> match (K KMoney) $> Q Money
        <|> match (K KBool)  $> Bit
 where
  row = fmap R $ some $ do
    p <- port
    spaced (match TypeColon)
    (p,) <$> stype

  vec :: Parser (SType' Raw)
  vec = do match (K KVec)
           (ty, n) <- round $ do
             ty <- stype
             spaced (match Comma)
             n <- unWC <$> cnoun
             pure (ty, n)
           pure $ Of ty n


thunkTy :: Parser RawVType
thunkTy = try (RC <$> ctype) <|> (RK <$> kernel)

ctype = do
  ins <- rawIO vtype
  spaced (match Arrow)
  outs <- rawIO vtype
  pure (ins :-> outs)

kernel :: Parser RawKType
kernel = do
  ins <- rawIO stype
  spaced (match Lolly)
  outs <- rawIO stype
  pure (ins :-> outs)

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

nbody :: String -> Parser (Clause Raw Noun)
nbody nm = do
  ident $ \x -> if x == nm then Just () else Nothing
  spaced $ match Equal
  body <- cnoun
  return $ NoLhs body


decl :: Parser RawDecl
decl = do
      (WC fc (nm, ty, body, rt)) <- withFC (do
        rt <- pure RtLocal -- runtime
        nm <- simpleName
        spaced $ match TypeColon
        (ty, body) <- try (do
            ty <- thunkTy <&> \ty -> [Named "thunk" ty]
            vspace
            (ty,) <$> ((ThunkOf <$> (withFC $ clauses nm)) <|> (nbody nm)))
          <|> (do
            ty <- outputs
            vspace
            (ty,) <$> nbody nm)
        pure (nm, ty, body, rt))
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
  fixLexErr :: ShowErrorComponent e
            => ParseErrorBundle String e -> Error
  fixLexErr er = let prettyErr = errorBundlePretty er
                     -- TODO: return all of the errors
                     e :| _errs = bundleErrors er
                     fc = mkFC (errorOffset e) (bundlePosState er)
                 in  Err (Just fc) (Just fname) $ LexErr (PE prettyErr)

  fixParseErr :: ShowErrorComponent e
              => ParseErrorBundle [Token] e -> Error
  fixParseErr er = let prettyErr = errorBundlePretty er
                       -- TODO: return all of the errors
                       e :| _errs = bundleErrors er
                       fc = mkFC (errorOffset e) (bundlePosState er)
                   in  Err (Just fc) (Just fname) $ ParseErr (PE prettyErr)


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
  branches = label "clauses" $
             fmap (Clauses . fromJust . nonEmpty) $
             some (try (vspace *> branch))

  branch = do
    label (declName ++ "(...) = ...") $
      ident $ \x -> if x == declName then Just () else Nothing
    space
    lhs <- withFC $ round (binding <?> "binder")
    spaced $ match Equal
    rhs <- cnoun
    pure (lhs,rhs)

  noLhs = label (declName ++ " = ...") $ do
    label declName $
      ident $ \x -> if x == declName then Just () else Nothing
    spaced (match Equal)
    NoLhs <$> cverb

pimport :: Parser UserName
pimport = kmatch KImport *> space *> userName

pstmt :: Parser RawEnv
pstmt = ((comment <?> "comment")                 <&> \_ -> ([] , []))
        <|> try ((alias <?> "type alias")        <&> \x -> ([] , [x]))
        <|> try (extVDecl                        <&> \x -> ([x], []))
        <|> try (extNDecl                        <&> \x -> ([x], []))
        <|> ((decl <?> "declaration")            <&> \x -> ([x], []))
 where
  alias :: Parser (UserName, TypeAlias)
  alias = withFC aliasContents <&>
          \(WC fc (alias, args, ty)) -> (plain alias, Alias fc alias args ty)


  aliasContents :: Parser (String, [UserName], RawVType)
  aliasContents = do
    match (K KType)
    hspace
    alias <- simpleName
    optional hspace
    args  <- fromMaybe [] <$> (optional . round $ (userName <* space) `sepBy` comma)
    spaced (match Equal)
    ty <- vtype' (mkParser <$> args)
    vspace
    let abstractTy = foldr (uncurry abstractVType) ty (zip args [0..])
    pure (alias, args, abstractTy)

  mkParser :: UserName -> Parser RawVType
  mkParser str = do
    name <- userName
    guard (name == str)
    pure $ RTypeFree name

  extNDecl :: Parser RawDecl
  extNDecl = do (WC fc (fnName, ty, symbol)) <- withFC $ do
                  match (K KExt)
                  space
                  symbol <- string
                  space
                  fnName <- simpleName
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

  extVDecl :: Parser RawDecl
  extVDecl = do (WC fc (fnName, ty, symbol)) <- withFC $ do
                  match (K KExt)
                  space
                  symbol <- string
                  space
                  fnName <- simpleName
                  spaced (match TypeColon)
                  ty <- thunkTy
                  optional hspace
                  vspace
                  pure (fnName, ty, symbol)
                pure Decl { fnName = fnName
                          , fnSig = [Named "thunk" ty]
                          , fnBody = Undefined
                          , fnLoc = fc
                          , fnRT = RtLocal
                          , fnLocality = Extern symbol
                          }

pfile :: Parser ([UserName], RawEnv)
pfile = do
  vspace
  imports <- many (pimport <* vspace)
  env     <- foldr (<>) ([], []) <$> ((pstmt <* vspace) `manyTill` eof)
  pure (imports, env)
