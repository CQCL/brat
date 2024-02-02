module Brat.Parser (parseFile) where

import Brat.Error
import Brat.FC
import Brat.Lexer
import Brat.Syntax.Common hiding (end)
import Brat.Syntax.Concrete
import Brat.Syntax.Raw
import Brat.Syntax.Simple
import Brat.UserName ( plain, UserName(..) )
import Brat.Elaborator

import Control.Monad (void)
import Control.Monad.State (State, evalState, runState, get, put)
import Data.Bifunctor
import Data.List.NonEmpty (toList, NonEmpty(..), nonEmpty)
import Data.Foldable (msum)
import Data.Functor (($>), (<&>))
import Data.Maybe (fromJust, maybeToList, fromMaybe)
import Data.Set (empty)
import Prelude hiding (lex, round)
import Text.Megaparsec hiding (Pos, Token, State, empty, match, ParseError, parse)
import qualified Text.Megaparsec as M (parse)

newtype CustomError = Custom String deriving (Eq, Ord)

-- the State is the (FC) Position of the last token *consumed*
type Parser a = ParsecT CustomError [Token] (State Pos) a

parse :: Parser a -> String -> [Token] -> Either (ParseErrorBundle [Token] CustomError) a
parse p s tks = evalState (runParserT p s tks) (Pos 0 0)

instance ShowErrorComponent CustomError where
  showErrorComponent (Custom s) = s


withFC :: Parser a -> Parser (WC a)
withFC p = do
  (Token (FC start _) _) <- nextToken
  thing <- p
  end <- get
  pure (WC (FC start end) thing)


nextToken :: Parser Token
nextToken = lookAhead $ token Just empty

token0 :: (Token -> Maybe a) -> Parser a
token0 x = do
  (Token fc _) <- nextToken
  r <- token x empty
  -- token matched condition x
  put (end fc)
  pure r

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
round p = label "(...)" $ match LParen *> p <* match RParen

square :: Parser a -> Parser a
square p = label "[...]" $ match LBracket *> p <* match RBracket

curly :: Parser a -> Parser a
curly p = label "{...}" $ match LBrace *> p <* match RBrace

inLet :: Parser a -> Parser a
inLet p = label "let ... in" $ kmatch KLet *> p <* kmatch KIn

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
comma = token0 $ \case
  Token _ Comma -> Just $ \a b ->
    let fc = FC (start (fcOf a)) (end (fcOf b))
    in  WC fc (FJuxt a b)
  _ -> Nothing

into :: Parser (WC Flat -> WC Flat -> WC Flat)
into = token0 $ \case
  Token _ Into -> Just $ \a b ->
    let fc = FC (start (fcOf a)) (end (fcOf b))
    in  WC fc (FInto a b)
  _ -> Nothing

arith :: ArithOp -> Parser (WC Flat -> WC Flat -> WC Flat)
arith op = token0 $ \(Token _ tok) -> case (op, tok) of
  (Add, Plus) -> Just make
  (Sub, Minus) -> Just make
  (Mul, Asterisk) -> Just make
  (Div, Slash) -> Just make
  (Pow, Caret) -> Just make
  _ -> Nothing
 where
  make a b = WC (FC (start (fcOf a)) (end (fcOf b))) (FArith op a b)

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
abstractor = do ps <- many (try portPull)
                xs <- binding `chainl1` try binderComma
                pure $ if null ps then xs else APull ps xs
 where
  binding :: Parser Abstractor
  binding = (try (APat <$> pat) <|> round abstractor)
  vecPat = square (binding `sepBy`  (match Comma)) >>= list2Cons

  list2Cons :: [Abstractor] -> Parser Pattern
  list2Cons [] = pure PNil
  list2Cons (APat x:xs) = PCons x <$> (list2Cons xs)
  list2Cons _ = customFailure (Custom "Internal error list2Cons")

  portPull = simpleName <* match PortColon

  binderComma :: Parser (Abstractor -> Abstractor -> Abstractor)
  binderComma = match Comma $> (:||:)

  pat :: Parser Pattern
  pat = try vecPat
    <|> (match Underscore $> DontCare)
    <|> try (Lit <$> simpleTerm)
    <|> try constructorsWithArgs
    <|> try nullaryConstructors
    <|> (Bind <$> simpleName)
   where
    constructor :: Parser Abstractor -> String -> Parser Pattern
    constructor pabs c = do
      matchString c
      PCon (plain c) <$> pabs

    nullaryConstructors = msum (try . constructor (pure AEmpty) <$> ["zero", "nil", "none", "true", "false"])

    constructorsWithArgs = msum (try . constructor (round abstractor) <$> ["succ", "doub", "cons", "some"])

simpleTerm :: Parser SimpleTerm
simpleTerm =
  (Text <$> string <?> "string")
  <|> try (Float . negate <$> (match Minus *> float) <?> "float")
  <|> try (Float <$> float <?> "float")
  <|> (Num . negate <$> (match Minus *> number) <?> "nat")
  <|> (Num <$> number <?> "nat")


outputs :: Parser [RawIO]
outputs = rawIO (unWC <$> vtype)

typekind :: Parser TypeKind
typekind = try (match Hash $> Nat) <|> ty
 where
  ty = do
    match Asterisk
    margs <- optional (round row)
    pure $ Star (concat $ maybeToList margs)

  row = (`sepBy` match Comma)  $ do
    p <- port
    match TypeColon
    (p,) <$> typekind

vtype :: Parser (WC (Raw Chk Noun))
vtype = cnoun atomExpr

-- Parse a row of type and kind parameters
-- N.B. kinds must be named
rawIO :: Parser ty -> Parser (TypeRow (KindOr ty))
rawIO tyP = rowElem `sepBy` void (try comma)
 where
  rowElem = try (round rowElem') <|> rowElem'

  rowElem' = try namedKind <|> try namedType <|> (Anon . Right <$> tyP)

  namedType = do
    p <- port
    match TypeColon
    Named p . Right <$> tyP

  namedKind = do
    p <- port
    match TypeColon
    Named p . Left <$> typekind

rawIO' :: Parser ty -> Parser (TypeRow ty)
rawIO' tyP = rowElem `sepBy` void (try comma)
 where
  rowElem = try (round rowElem') <|> rowElem'

  -- Look out if we can find ::. If not, backtrack and just do tyP.
  -- For example, if we get an invalid primitive type (e.g. `Int` in
  -- a kernel or a misspelled type like `Intt`), we get the better
  -- error message from tyP instead of complaining about a missing ::
  -- (since the invalid type can be parsed as a port name)
  rowElem' = optional (try $ port <* match TypeColon) >>= \case
       Just p -> Named p <$> tyP
       Nothing -> Anon <$> tyP

stype :: Parser (SType' (Raw Chk Noun))
stype = try (Rho <$> round row)
        <|> try vec
        <|> match (K KQubit) $> Q Qubit
        <|> match (K KMoney) $> Q Money
        <|> match (K KBool)  $> Bit
 where
  row = fmap R $ (`sepBy` match Comma) $ do
    p <- port
    match TypeColon
    (p,) <$> stype

  vec :: Parser (SType' (Raw Chk Noun))
  vec = label "Vec" $ do
    ident (\x -> if x == "Vec" then Just () else Nothing)
    (ty, n) <- round $ do
      ty <- stype
      match Comma
      n <- unWC <$> cnoun atomExpr
      pure (ty, n)
    pure $ Of ty n

functionType :: Parser RawVType
functionType = try (RFn <$> ctype) <|> (RKernel <$> kernel)
 where
  ctype :: Parser RawCType
  ctype = do
    ins <- round $ rawIO (unWC <$> vtype)
    match Arrow
    outs <- rawIO (unWC <$> vtype)
    pure (ins :-> outs)

  kernel :: Parser RawKType
  kernel = do
    ins <- round $ rawIO' stype
    match Lolly
    outs <- rawIO' stype
    pure (ins :-> outs)


vec :: Parser Flat
vec = (\(WC fc x) -> unWC $ vec2Cons (end fc) x) <$>  withFC (square elems)
  where
    elems = (element `chainl1` (try vecComma)) <|> pure []
    vecComma = match Comma $> (++)
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
cthunk = try bratFn <|> try kernel <|> thunk
 where
  bratFn = curly $ do
    ss <- rawIO (unWC <$> vtype)
    match Arrow
    ts <- rawIO (unWC <$> vtype)
    pure $ FFn (ss :-> ts)

  kernel = curly $ do
    ss <- rawIO' stype
    match Lolly
    ts <- rawIO' stype
    pure $ FKernel (ss :-> ts)

  -- Explicit lambda or brace section
  thunk = FThunk <$> withFC (curly (try abstracted
                                    <|> braceSection))

  abstracted = do
    abs <- withFC $ (try  abstractor <|> pure AEmpty)
    match FatArrow
    FLambda abs <$> withFC expr

  braceSection = do
    e <- withFC expr
    -- Replace underscores with invented variable names '1, '2, '3 ...
    -- which are illegal for the user to use as variables
    case runState (replaceU e) 0 of
      (e', 0) -> pure (unWC e')
      -- If we don't have a `=>` at the start of a kernel, it could (and should)
      -- be a verb, not the RHS of a no-arg lambda
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
-- precedence than juxtaposition). Precedence table (loosest to tightest binding):
--    + -  (left-assoc)
--    * /  (left-assoc)
--    ^    (left-assoc)
--    ::   (no associativity, i.e. explicit parenthesis required for chaining)
--    app  (left-assoc)
atomExpr :: Parser Flat
atomExpr = atomExpr' 0
 where
  atomExpr' n = choice $ drop n [
    try (addSub <?> "addition or subtraction"),
    try (mulDiv <?> "multiplication or division"),
    try (pow <?> "power"),
    try (annotation <?> "type annotation"),
    try (app <?> "application"),
    simpleExpr,
    round expr ]

  binary ops lvl = unWC <$> withFC (atomExpr' lvl) `chainl1` choice (try . arith <$> ops)
  addSub = binary [Add, Sub] 1
  mulDiv = binary [Mul, Div] 2
  pow = binary [Pow] 3

  annotation = FAnnotation <$> withFC (atomExpr' 4) <* match TypeColon <*> rawIO (unWC <$> vtype)

  app = withFC (atomExpr' 5) >>= applied
  applied :: WC Flat -> Parser Flat
  applied f = do
    first <- withFC (round $ expr <|> pure FEmpty)
    let one = FApp f first
    let combinedFC = FC (start (fcOf f)) (end (fcOf first))
    optional (applied $ WC combinedFC one) <&> fromMaybe one

  simpleExpr = FHole <$> hole
            <|> try (FSimple <$> simpleTerm)
            <|> vec
            <|> cthunk
            <|> (withFC (kmatch KBool) <&> \(WC fc _) -> FCon (plain "Bool") (WC fc FEmpty))
            <|> try (match DotDot $> FPass)
            <|> var
            <|> match Underscore $> FUnderscore


{- Infix operator precedence table
(loosest to tightest binding):
   =>
   |> (left-assoc)
   ;
   , & port-pull
   atomExpr
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
      match Equal
      thing <- withFC (try letin <|> expr' 1)
      pure (abs, thing)
    body <- withFC (try letin <|> expr' 1)
    pure $ FLetIn lhs rhs body

  lambda = do
    abs <- withFC abstractor
    match FatArrow
    body <- withFC (try lambda <|> expr' 2)
    pure (FLambda abs body)

  cinto = unWC <$> withFC (expr' 3 <|> pure FEmpty) `chainl1` try into

  composition = unWC <$> withFC (expr' 4) `chainl1` try semicolon

  pull = do
    ports <- some (try (port <* match PortColon))
    FPull ports <$> withFC (expr' 5)

  juxt = unWC <$> withFC (try pull <|> expr' 6) `chainl1` try comma

  semicolon :: Parser (WC Flat -> WC Flat -> WC Flat)
  semicolon = token0 $ \case
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
        ty <- try (functionType <&> \ty -> [Named "thunk" (Right ty)])
              <|> (match TypeColon >> outputs)
        let allow_clauses = case ty of
                                 [Named _ (Right t)] -> is_fun_ty t
                                 [Anon (Right t)] -> is_fun_ty t
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
      is_fun_ty (RFn _) = True
      is_fun_ty (RKernel _) = True
      is_fun_ty _ = False

      nbody :: String -> Parser (WC Flat)
      nbody nm = do
        label (nm ++ "(...) = ...") $
          matchString nm
        match Equal
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

parseFile :: String -> String -> Either SrcErr ([Import], FEnv)
parseFile fname contents = addSrcContext fname contents $ do
  toks <- first (wrapParseErr LexErr) (M.parse lex fname contents)
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
                   some (try branch)
 where
  branch = do
    label (declName ++ "(...) = ...") $
      matchString declName
    lhs <- withFC $ round (abstractor <?> "binder")
    match Equal
    rhs <- withFC expr
    pure (lhs,rhs)

pimport :: Parser Import
pimport = do
  o <- open
  kmatch KImport
  x <- withFC userName
  a <- alias
  s <- selection
  pure (Import x (not o) a s)
 where
  open :: Parser Bool
  open = optional (matchString "open") >>= \case
     Nothing -> pure False
     Just _ -> pure True

  alias :: Parser (Maybe (WC String))
  alias = optional (matchString "as") >>= \case
     Nothing -> pure Nothing
     Just _ -> Just <$> withFC (ident Just)

  selection :: Parser ImportSelection
  selection = optional (try $ matchString "hiding") >>= \case
    Just _ -> ImportHiding <$> list
    Nothing -> optional list >>= \case
       Nothing -> pure ImportAll
       Just ss -> pure (ImportPartial ss)

  list :: Parser [WC String]
  list = round $ ((:[]) <$> withFC (ident Just)) `chainl1` try (match Comma $> (++))

pstmt :: Parser FEnv
pstmt = ((comment <?> "comment")                 <&> \_ -> ([] , []))
        <|> try ((alias <?> "type alias")        <&> \x -> ([] , [x]))
        <|> try (extDecl                         <&> \x -> ([x], []))
        <|> ((decl <?> "declaration")            <&> \x -> ([x], []))
 where
  alias :: Parser RawAlias
  alias = withFC aliasContents <&>
          \(WC fc (name, args, ty)) -> (TypeAlias fc name args ty)

  aliasContents :: Parser (UserName, [(String, TypeKind)], RawVType)
  aliasContents = do
    match (K KType)
    alias <- userName
    args <- option [] $ round $ (simpleName `sepBy` (match Comma))
{- future stuff
    args <- option [] $ round $ (`sepBy` (match Comma)) $ do
      port <- port
      match TypeColon
      (port,) <$> typekind
-}
    match Equal
    ty <- vtype
    -- TODO: Right now we restrict the variables in a type alias to being of
    -- kind `Star []` (i.e. the type of simple types). In future we should allow
    -- users to specify the kinds of variables in type aliases, like:
    --   type X(a :: *, b :: #, c :: *(x :: *, y :: #)) = ...
    -- See KARL-325
    pure (alias, (,Star []) <$> args, unWC ty)

  extDecl :: Parser FDecl
  extDecl = do (WC fc (fnName, ty, symbol)) <- withFC $ do
                  match (K KExt)
                  symbol <- string
                  fnName <- simpleName
                  ty <- try nDecl <|> vDecl
                  pure (fnName, ty, symbol)
               pure Decl { fnName = fnName
                         , fnSig = ty
                         , fnBody = FUndefined
                         , fnLoc = fc
                         , fnRT = RtLocal
                         , fnLocality = Extern symbol
                         }
   where
    nDecl = match TypeColon >> outputs
    vDecl = (:[]) . Named "thunk" . Right <$> functionType

pfile :: Parser ([Import], FEnv)
pfile = do
  imports <- many pimport
  env     <- foldr (<>) ([], []) <$> (pstmt `manyTill` eof)
  pure (imports, env)
