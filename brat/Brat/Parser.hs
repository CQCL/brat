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
import Prelude hiding (lex, round)
import Text.Megaparsec hiding (Pos, Token, empty, match)

newtype CustomError = Custom String deriving (Eq, Ord)

type Parser a = Parsec CustomError [Token] a

instance ShowErrorComponent CustomError where
  showErrorComponent (Custom s) = s

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

matchString :: String -> Parser ()
matchString s = ident $ \x -> if x == s then Just () else Nothing

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

thunk :: (FC -> Thunk -> Maybe a) -> Parser a
thunk f = label "{...}" $ token0 $ \case
  Token fc (Curly th) -> f fc th
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
                   <|> try nestedBinding
                   <|> try vecLit
                   <|> try (Lit <$> simpleTerm)
                   <|> (Bind <$> simpleName)) `chainl1` (try binderComma)
             if null ps
               then pure xs
               else pure $ APull ps xs
 where
  vecLit = list2Cons <$> square (binding `sepBy` (spaced (match VecComma)))

  list2Cons :: [Abstractor] -> Abstractor
  list2Cons [] = Pat PNil
  list2Cons (x:xs) = Pat (PCons (x :||: list2Cons xs))

  portPull = simpleName <* match PortColon

  nestedBinding = round binding

  binderComma :: Parser (Abstractor -> Abstractor -> Abstractor)
  binderComma = spaced $ match Comma $> (:||:)

pat :: Parser a -> Parser (Pattern a)
pat p = try onePlus
      <|> try twoTimes
      <|> try (matchString "nil" $> PNil)
      <|> try cons
      <|> try (matchString "none" $> PNone)
      <|> try psome
 where
  psome = do
    matchString "some"
    space
    PSome <$> round p

  cons = do
    matchString "cons"
    space
    PCons <$> round p

  onePlus = do
    matchString "succ"
    space
    POnePlus <$> round p

  twoTimes = do
    matchString "doub"
    space
    PTwoTimes <$> round p

sverb :: Parser (WC (Raw Syn Verb))
sverb = (juxtaposition sverb') `chainl1` try semicolon
 where
  sverb' :: Parser (WC (Raw Syn Verb))
  -- note: we might need (round sverb) as an option here too
  sverb' = try (letin sverb) <|> withFC (try (func snoun) <|> force)

  force :: Parser (Raw Syn Verb)
  force = RForce <$> (snoun <* spaced (round (space *> eof)))

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

cverb :: Parser (WC (Raw Chk Verb))
-- try to parse an sverb;cverb first. If that fails to find a semicolon,
-- the sverb can be reparsed as a cverb
cverb = try (withFC $ compose sverb cverb) <|> (juxtaposition cverb')
 where
  cverb' :: Parser (WC (Raw Chk Verb))
  cverb' = try (letin cverb <?> "let binding") <|> withFC
    (try (func cnoun <?> "function")
    <|> try (RVHole <$> hole <?> "typed hole")
    <|> (REmb <$> sverb <?> "syn verb")
    ) <|> round cverb


var :: Parser (Raw Syn Noun)
var = RVar <$> userName

snoun' :: Parser (WC (Raw Syn Noun))
snoun' = withFC $ do
  sn <- round snoun <|> letin snoun <|> withFC var
  try (application sn) <|> pure (unWC sn)
 where
  application :: WC (Raw Syn Noun) -> Parser (Raw Syn Noun)
  application fun = do
    space
    arg <- round cnoun
    pure (fun ::$:: arg)

snoun :: Parser (WC (Raw Syn Noun))
snoun = do
  sn <- juxtaposition snoun'
  -- snoun;sverb is an snoun, so look for trailing ;sverb
  -- we only need to look for one since sverb;sverb is itself an sverb
  (fromMaybe sn) <$> (optional $ do
    f <- try semicolon
    sv <- sverb
    return $ f sn sv)

compose :: Parser (WC (Raw Syn k)) -> Parser (WC (Raw d Verb)) -> Parser (Raw d k)
compose p1 p2 = do
  x <- p1
  spaced (match Semicolon) <?> "semicolon"
  y <- p2
  pure (x ::-:: y)

simpleTerm :: Parser SimpleTerm
simpleTerm =
  ((Text <$> string <?> "string")
  <|> try (Float <$> float <?> "float")
  <|> (Num <$> number <?> "nat")
  <|> (bool <?> "bool"))
  <|> (match UnitElem $> Unit)
 where
  bool :: Parser SimpleTerm
  bool = Bool <$> (matchString "true" $> True
                   <|> matchString "false" $> False)

cnoun' :: Parser (WC (Raw Chk Noun))
cnoun' = try (letin cnoun) <|> withFC
  (try (cthunk <?> "thunk")
  <|> try (pull <?> "port pull")
  <|> try (vec <?> "vector literal")
  <|> (nhole <?> "hole")
  <|> try (RSimple <$> simpleTerm)
  <|> try emb
  ) <|> round cnoun
 where

  nhole = RNHole <$> hole

  pull = do
    ports <- some (try (port <* match PortColon))
    RPull ports <$> cnoun

  emb = REmb <$> snoun'

  cthunk :: Parser (Raw Chk Noun)
  cthunk = thunk $ \fc th -> case th of
    Thunk n ss -> RTh <$> braceSection fc n ss
    Lambda ss ts -> RTh . WC fc <$> ((::\::) <$> parseMaybe (spaced (withFC binding)) ss <*> parseMaybe (spaced cnoun) ts)
    _ -> Nothing

  -- Invented variable names look like '1, '2, '3 ...
  -- which are illegal for the user to use as variables
  braceSectionAbstractor :: [Int] -> Abstractor
  braceSectionAbstractor ns = foldr (:||:) AEmpty (Bind . ('\'':) . show <$> ns)

  braceSection :: FC -> Int -> [Token] -> Maybe (WC (Raw Chk Verb))
  braceSection _ 0 ts | Just v <- parseMaybe (spaced cverb) ts = Just v
  braceSection fc n ts = do
   let abs = WC fc (braceSectionAbstractor [0..n-1])
   body <- parseMaybe (spaced cnoun) ts
   pure (WC fc (abs ::\:: body))

  mkNil :: FC -> Raw Chk Noun
  mkNil fc = RCon (plain "nil") (WC fc REmpty)

  vec2Cons :: Pos -> [WC (Raw Chk Noun)] -> WC (Raw Chk Noun)
  -- The nil element gets as FC the closing ']' of the [li,te,ral]
  vec2Cons end [] = let fc = FC end{col=(col end)-1} end in WC fc (mkNil fc)
  -- We give each cell of the list an FC which starts with the FC
  -- of its head element and ends at the end of the list (the closing ']')
  vec2Cons end (x:xs) = let fc = FC (start $ fcOf x) end in
    WC fc $ RCon (plain "cons") (WC fc (x ::|:: (vec2Cons end xs)))

  vec :: Parser (Raw Chk Noun)
  vec = (\(WC fc x) -> unWC $ vec2Cons (end fc) x) <$> withFC (square elems)
   where
    elems = (eof $> []) <|> (element `chainl1` (try vecComma))
    vecComma = spaced (match VecComma) $> (++)
    element = (:[]) <$> cnoun'

cnoun :: Parser (WC (Raw Chk Noun))
cnoun = try (withFC $ nounIntoVerb) <|> juxtaposition cnoun'
 where
  -- try nounIntoVerb first: the leading (juxtaposition snoun')
  -- can definitely be reparsed as a (juxtaposition cnoun')
  -- if we fail to find a semicolon. We look for (juxtaposition snoun')
  -- rather than snoun because anything after a semicolon would be parsed
  -- by snoun as an sverb, but here we can allow (more flexible) cverb.
  nounIntoVerb :: Parser (Raw Chk Noun)
  nounIntoVerb = compose (juxtaposition snoun') cverb

outputs :: Parser [RawIO]
outputs = rawIO vtype


vtype :: Parser RawVType
vtype = vtype' []

vtype' :: [Parser RawVType] -> Parser RawVType
vtype' ps = try (round vty) <|> vty
 where
  vty = try thunkType
    <|> choice (try <$> ps)
    <|> try vec
    <|> simple
    <|> try alias
    <|> typeVar

  typeVar = RTypeFree <$> userName

  alias = try aliasWithArgs <|> justAlias

  justAlias = RAlias <$> userName <*> pure []

  aliasWithArgs = do
    alias <- userName
    space
    args <- round $ vtype' ps `sepBy` comma
    pure $ RAlias alias args

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

  thunkType = thunk $ \_ th -> case th of
    Kernel ss ts -> RK <$> ((:->) <$> parseMaybe (spaced (rawIO stype)) ss <*> parseMaybe (spaced (rawIO stype)) ts)
    FunTy  ss ts -> RC <$> ((:->) <$> parseMaybe (spaced (rawIO vtype)) ss <*> parseMaybe (spaced (rawIO vtype)) ts)
    -- Don't allow brace sections as types yet
    Thunk 0 ss -> RC . ([] :->) <$> parseMaybe (spaced (rawIO vtype)) ss
    _ -> Nothing


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
  row = fmap R $ (`sepBy` spaced (match Comma)) $ do
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


functionType :: Parser RawVType
functionType = try (RC <$> ctype) <|> (RK <$> kernel)
 where
  ctype = do
    ins <- round $ rawIO vtype
    spaced (match Arrow)
    outs <- rawIO vtype
    pure (ins :-> outs)

  kernel :: Parser RawKType
  kernel = do
    ins <- round $ rawIO stype
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
  matchString nm
  spaced $ match Equal
  body <- cnoun
  return $ NoLhs body


decl :: Parser RawDecl
decl = do
      (WC fc (nm, ty, body, rt)) <- withFC (do
        rt <- pure RtLocal -- runtime
        nm <- simpleName
        space
        ty <- try (functionType <&> \ty -> [Named "thunk" ty])
              <|> (spaced (match TypeColon) >> outputs)
        vspace
        let allow_clauses = case ty of
                                 [Named _ t] -> is_fun_ty t
                                 [Anon t] -> is_fun_ty t
                                 _ -> False
        body <- (if allow_clauses
          then (ThunkOf <$> (withFC $ clauses nm)) <|> (nbody nm)
          else (nbody nm))
        pure (nm, ty, body, rt))
      pure $ Decl { fnName = nm
                  , fnLoc  = fc
                  , fnSig  = ty
                  , fnBody = body
                  , fnRT   = rt
                  , fnLocality = Local
                  }
    where
      is_fun_ty :: RawVType -> Bool
      is_fun_ty (RC _) = True
      is_fun_ty (RK _) = True
      is_fun_ty _ = False

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
      matchString declName
    space
    lhs <- withFC $ round (binding <?> "binder")
    spaced $ match Equal
    rhs <- cnoun
    pure (lhs,rhs)

  noLhs = label (declName ++ " = ...") $ do
    label declName $
      matchString declName
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
                  space
                  ty <- functionType
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
