module Brat.Parser (parseFile) where

import Brat.Error
import Brat.FC
import Brat.Lexer
import Brat.Syntax.Common hiding (K, end)
import Brat.Syntax.Concrete
import Brat.Syntax.Raw
import Brat.UserName ( plain, UserName(..) )
import Brat.Elaborator

import Control.Monad.State
import Data.Bifunctor
import Data.List.NonEmpty (toList, NonEmpty(..), nonEmpty)
import Data.Functor (($>), (<&>))
import Data.Maybe (fromJust, fromMaybe)
import Data.Set (empty)
import Prelude hiding (lex, round)
import Text.Megaparsec hiding (Pos, Token, empty, match, ParseError, State)

newtype CustomError = Custom String deriving (Eq, Ord)

type Parser a = Parsec CustomError [Token] a

instance ShowErrorComponent CustomError where
  showErrorComponent (Custom s) = s


withFC :: Parser a -> Parser (WC a)
withFC p = do
  (Token (FC start _) _) <- nextToken
  thing <- p
  eof <- optional eof
  case eof of
    Just _ -> pure (WC (FC start start) thing)
    Nothing -> do (Token (FC end _) _) <- nextToken
                  pure (WC (FC start end) thing)


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
round p = label "(...)" $ match LParen *> spaced p <* match RParen

square :: Parser a -> Parser a
square p = label "[...]" $ match LBracket *> spaced p <* match RBracket

curly :: Parser a -> Parser a
curly p = label "{...}" $ match LBrace *> spaced p <* match RBrace

inLet :: Parser a -> Parser a
inLet p = label "let ... in" $ kmatch KLet *> spaced p <* kmatch KIn

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

var :: Parser Flat
var = FVar <$> userName

port = simpleName

comma :: Parser (WC Flat -> WC Flat -> WC Flat)
comma = spaced $ token0 $ \case
  Token _ Comma -> Just $ \a b ->
    let fc = FC (start (fcOf a)) (end (fcOf b))
    in  WC fc (FJuxt a b)
  _ -> Nothing

into :: Parser (WC Flat -> WC Flat -> WC Flat)
into = spaced $ token0 $ \case
  Token _ Into -> Just $ \a b ->
    let fc = FC (start (fcOf a)) (end (fcOf b))
    in  WC fc (FInto a b)
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

abstractor :: Parser Abstractor
abstractor = do ps <- many (try $ portPull <* space)
                xs <- binding `chainl1` try binderComma
                pure $ if null ps then xs else APull ps xs
 where
  binding :: Parser Abstractor
  binding = (try (APat <$> pat) <|> round abstractor)
  vecPat = square (binding `sepBy` (spaced (match Comma))) >>= list2Cons

  list2Cons :: [Abstractor] -> Parser Pattern
  list2Cons [] = pure PNil
  list2Cons (APat x:xs) = PCons x <$> (list2Cons xs)
  list2Cons _ = customFailure (Custom "Internal error list2Cons")

  portPull = simpleName <* match PortColon

  binderComma :: Parser (Abstractor -> Abstractor -> Abstractor)
  binderComma = spaced $ match Comma $> (:||:)

  pat :: Parser Pattern
  pat = try vecPat
    <|> (match Underscore $> DontCare)
    <|> try (Lit <$> simpleTerm)
    <|> try onePlus
    <|> try twoTimes
    <|> try (matchString "nil" $> PNil)
    <|> try cons
    <|> try (matchString "none" $> PNone)
    <|> try psome
    <|> (Bind <$> simpleName)
   where
    psome = do
      matchString "some"
      space
      PSome <$> round pat

    cons = do
      matchString "cons"
      space
      PCon "cons" <$> round abstractor

    onePlus = do
      matchString "succ"
      space
      POnePlus <$> round pat

    twoTimes = do
      matchString "doub"
      space
      PTwoTimes <$> round pat

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


outputs :: Parser [RawIO]
outputs = rawIO vtype

vtype :: Parser RawVType
vtype = vtype' []

vtype' :: [Parser RawVType] -> Parser RawVType
vtype' ps = try (round vty) <|> vty
 where
  vty = thunkType  -- No try here! We commit to thunk if we see a {
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

  vec = kmatch KVec *> space *> round (RVector <$> vtype' ps <* spaced comma <*> cnoun atomExpr)

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

  -- Don't allow brace sections as types yet
  thunkType = curly (try kernel <|> funTy)
   where
    kernel = do
      ss <- spaced (rawIO stype)
      match Lolly
      ts <- spaced (rawIO stype)
      pure $ RK (ss :-> ts)

    funTy = do
      ss <- spaced (rawIO vtype)
      match Arrow
      ts <- spaced (rawIO vtype)
      pure $ RC (ss :-> ts)


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
             n <- unWC <$> cnoun atomExpr
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


vec :: Parser Flat
vec = (\(WC fc x) -> unWC $ vec2Cons (end fc) x) <$>  withFC (square elems)
  where
    elems = (element `chainl1` (try vecComma)) <|> pure []
    vecComma = spaced (match Comma) $> (++)
    element = (:[]) <$> withFC atomExpr
    mkNil fc = FCon (plain "nil") (WC fc FEmpty)

    vec2Cons :: Pos -> [WC Flat] -> WC Flat
    -- The nil element gets as FC the closing ']' of the [li,te,ral]
    vec2Cons end [] = let fc = FC end{col=(col end)-1} end in WC fc (mkNil fc)
    -- We give each cell of the list an FC which starts with the FC
    -- of its head element and ends at the end of the list (the closing ']')
    vec2Cons end (x:xs) = let fc = FC (start $ fcOf x) end in
      WC fc $ FCon (plain "cons") (WC fc (FJuxt x (vec2Cons end xs)))


cthunk :: Parser Flat
cthunk = FThunk <$> withFC (curly (try abstracted <|> braceSection))  -- Explicit lambda or brace section
 where
  abstracted = do
    abs <- try (spaced (withFC abstractor)) <|> withFC (pure AEmpty)
    match FatArrow
    e <- spaced (withFC expr)
    pure $ FLambda abs e

  braceSection = do
    e <- withFC expr
    -- Replace underscores with invented variable names '1, '2, '3 ...
    -- which are illegal for the user to use as variables
    case runState (replaceU e) 0 of
      (e', 0) -> pure (unWC e')
      (e', n) -> let abs = braceSectionAbstractor [0..n-1] in
                 pure $ FLambda (WC (fcOf e) abs) e'  -- TODO: Which FC to use for the abstracor?

  replaceU :: WC Flat -> State Int (WC Flat)
  replaceU (WC fc x) = WC fc <$> replaceU' x

  replaceU' :: Flat -> State Int Flat
  replaceU' FUnderscore = do
    n <- get
    put (n+1)
    pure $ FVar (PrefixName [] ('\'':show n))
  replaceU' (FThunk a) = pure $ FThunk a  -- Don't recurse into thunks!
  replaceU' (FApp a b) = FApp <$> replaceU a <*> replaceU b
  replaceU' (FJuxt a b) = FJuxt <$> replaceU a <*> replaceU b
  replaceU' (FCompose a b) = FCompose <$> replaceU a <*> replaceU b
  replaceU' (FInto a b) = FInto <$> replaceU a <*> replaceU b
  replaceU' (FLetIn abs a b) = FLetIn abs <$> replaceU a <*> replaceU b
  replaceU' (FLambda abs a) = FLambda abs <$> replaceU a
  replaceU' (FAnnotation a t) = (`FAnnotation` t) <$> replaceU a
  replaceU' (FCon x a) = FCon x <$> replaceU a
  replaceU' (FPull ps a) = FPull ps <$> replaceU a
  replaceU' x = pure x

  braceSectionAbstractor :: [Int] -> Abstractor
  braceSectionAbstractor ns = foldr (:||:) AEmpty $
                              (\x -> APat (Bind ('\'': show x))) <$> ns


-- Expressions that can occur inside juxtapositions and vectors (i.e. everything with a higher
-- precedence than juxtaposition).
atomExpr :: Parser Flat
atomExpr = atomExpr' 0
 where
  atomExpr' n = choice $ drop n [
    try (annotation <?> "type annotation"),
    try (app <?> "application"),
    simpleExpr,
    round expr ]

  annotation = FAnnotation <$> withFC (atomExpr' 1) <* spaced (match TypeColon) <*> rawIO vtype

  app = FApp <$> withFC (atomExpr' 2) <* space <*> withFC (round expr)

  simpleExpr = FHole <$> hole
            <|> try (FSimple <$> simpleTerm)
            <|> vec
            <|> cthunk
            <|> var
            <|> match Underscore $> FUnderscore


{- Infix operator precedence table
(loosest to tightest binding):
   =>
   |> (left-assoc)
   ;
   , & port-pull
   ::
-}
expr :: Parser Flat
expr = expr' 0
 where
  expr' :: Int -> Parser Flat
  expr' n = choice $ drop n [
    try (letin <?> "let ... in"),
    try (lambda <?> "abstraction"),
    try (cinto <?> "into"),
    try (composition <?> "composition"),
    try (pull <?> "port pull"),
    try (juxt <?> "juxtaposition"),
    atomExpr ]

  letin = do
    (lhs,rhs) <- inLet $ do
      abs <- withFC abstractor
      spaced $ match Equal
      thing <- withFC (try letin <|> expr' 1)
      pure (abs, thing)
    space
    body <- withFC (try letin <|> expr' 1)
    pure $ FLetIn lhs rhs body

  lambda = do
    abs <- withFC abstractor
    spaced (match FatArrow)
    body <- withFC (try lambda <|> expr' 2)
    pure (FLambda abs body)

  cinto = unWC <$> withFC (expr' 3) `chainl1` try into

  composition = unWC <$> withFC (expr' 4) `chainl1` try semicolon

  pull = do
    ports <- some (try (port <* match PortColon))
    FPull ports <$> withFC (expr' 5)

  juxt = unWC <$> withFC (try pull <|> expr' 6) `chainl1` try comma

  semicolon :: Parser (WC Flat -> WC Flat -> WC Flat)
  semicolon = spaced $ token0 $ \case
    Token _ Semicolon -> Just $ \a b ->
      let fc = FC (start (fcOf a)) (end (fcOf b))
      in  WC fc (FCompose a b)
    _ -> Nothing


cnoun :: Parser Flat -> Parser (WC (Raw 'Chk 'Noun))
cnoun pe = do
  e <- withFC pe
  case elaborate e of
    Left err -> fail (showError err)
    Right (SomeRaw r) -> case do
      r <- assertChk r
      r <- assertNoun r
      pure r
     of
      Left err -> fail (showError err)
      Right r -> pure r


decl :: Parser FDecl
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
        body <- if allow_clauses then (FClauses <$> clauses nm) <|> (FNoLhs <$> nbody nm)
                else FNoLhs <$> nbody nm
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

      nbody :: String -> Parser (WC Flat)
      nbody nm = do
        label (nm ++ "(...) = ...") $
          matchString nm
        spaced $ match Equal
        withFC expr

class FCStream a where
  getFC :: Int -> PosState a -> FC

sp_to_fc :: SourcePos -> FC
sp_to_fc (SourcePos _ line col) = let
  l = unPos line
  c = unPos col
 in FC (Pos l c) (Pos l (c + 1))

instance FCStream String where
  getFC os pst = let (_, pst') = reachOffset os pst in sp_to_fc $ pstateSourcePos pst'

instance FCStream [Token] where
  getFC o PosState{..} = case drop (o - pstateOffset) pstateInput of
    [] -> sp_to_fc pstateSourcePos
    (Token fc _):_ -> fc

parseFile :: String -> String -> Either SrcErr ([UserName], FEnv)
parseFile fname contents = addSrcContext fname contents $ do
  toks <- first (wrapParseErr LexErr) (parse lex fname contents)
  first (wrapParseErr ParseErr) (parse pfile fname toks)
 where
  wrapParseErr :: (VisualStream t, FCStream t, ShowErrorComponent e)
               => (ParseError -> ErrorMsg) -> ParseErrorBundle t e -> Error
  wrapParseErr wrapper er = let
      -- TODO: return all of the errors? There is generally only one.
      e :| errs = bundleErrors er
      prettyErr = (parseErrorTextPretty e) ++ case errs of
        [] -> ""
        xs -> " and " ++ (show $ length xs) ++ " other errors"
      fc = getFC (errorOffset e) (bundlePosState er)
    in  Err (Just fc) $ wrapper (PE prettyErr)

clauses :: String -> Parser (NonEmpty (WC Abstractor, WC Flat))
clauses declName = label "clauses" $
                   fmap (fromJust . nonEmpty) $
                   some (try (vspace *> branch))
 where
  branch = do
    label (declName ++ "(...) = ...") $
      matchString declName
    space
    lhs <- withFC $ round (abstractor <?> "binder")
    spaced $ match Equal
    rhs <- withFC expr
    pure (lhs,rhs)

pimport :: Parser UserName
pimport = kmatch KImport *> space *> userName

pstmt :: Parser FEnv
pstmt = ((comment <?> "comment")                 <&> \_ -> ([] , []))
        <|> try ((alias <?> "type alias")        <&> \x -> ([] , [x]))
        <|> try (extDecl                         <&> \x -> ([x], []))
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

  extDecl :: Parser FDecl
  extDecl = do (WC fc (fnName, ty, symbol)) <- withFC $ do
                  match (K KExt)
                  space
                  symbol <- string
                  space
                  fnName <- simpleName
                  ty <- try nDecl <|> vDecl
                  optional hspace
                  vspace
                  pure (fnName, ty, symbol)
               pure Decl { fnName = fnName
                         , fnSig = ty
                         , fnBody = FUndefined
                         , fnLoc = fc
                         , fnRT = RtLocal
                         , fnLocality = Extern symbol
                         }
   where
    nDecl = spaced (match TypeColon) >> outputs
    vDecl = (:[]) . Named "thunk" <$> (space >> functionType)

pfile :: Parser ([UserName], FEnv)
pfile = do
  vspace
  imports <- many (pimport <* vspace)
  env     <- foldr (<>) ([], []) <$> ((pstmt <* vspace) `manyTill` eof)
  pure (imports, env)
