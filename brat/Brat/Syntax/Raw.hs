{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Brat.Syntax.Raw where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (intercalate)
import Data.Kind (Type)

import Brat.Error
import Brat.FC
import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.UserName
import Util (names)

type family TypeOf (k :: Kind) :: Type where
  TypeOf Noun = [InOut]
  TypeOf Verb = CType

data RawVType
  = RC RawCType
  | RSimpleTy SimpleType
  | RList RawVType
  | RProduct RawVType RawVType
  | RAlias UserName [RawVType]
  | RTypeFree UserName
  | RTypeVar Int
  | RVector RawVType (WC (Raw Chk Noun))
  | RThinning (WC (Raw Chk Noun)) (WC (Raw Chk Noun))
  | RK (Row Raw) (Row Raw)
  | ROption RawVType
  deriving (Eq, Show)

data RawIO' ty = Named Port ty | Anon ty deriving (Functor, Show)

instance Eq ty => Eq (RawIO' ty) where
  Named _ ty == Named _ ty' = ty == ty'
  Anon ty == Named _ ty' = ty == ty'
  Named _ ty == Anon ty' = ty == ty'
  Anon ty == Anon ty' = ty == ty'

type RawIO = RawIO' RawVType

type RawCType = CType' RawIO

deriving instance Eq RawCType

data TypeAlias = Alias FC String [UserName] RawVType deriving (Eq, Show)

type RawDecl = Decl' RawIO Raw
type RawEnv = ([RawDecl], [(UserName, TypeAlias)])

type RawSlice = Slice (WC (Raw Chk Noun))

data Raw :: Dir -> Kind -> Type where
  RLet      :: WC Abstractor -> WC (Raw Syn Noun) -> WC (Raw d k) -> Raw d k
  RNHole    :: String -> Raw Chk Noun
  RVHole    :: String -> Raw Chk Verb
  RSimple   :: SimpleTerm -> Raw Chk Noun
  (::|::)   :: WC (Raw d k) -> WC (Raw d k) -> Raw d k
  RTh       :: WC (Raw Chk Verb) -> Raw Chk Noun
  REmb      :: WC (Raw Syn k) -> Raw Chk k
  RPull     :: [Port] -> WC (Raw Chk k) -> Raw Chk k
  RVar      :: UserName -> Raw Syn Noun
  (::$::)   :: WC (Raw Syn Noun) -> WC (Raw Chk Noun) -> Raw Syn Noun -- Eval with ChkRaw n argument
  (:::::)   :: WC (Raw Chk k) -> [RawIO] -> Raw Syn k
  (::-::)   :: WC (Raw Syn k) -> WC (Raw d Verb) -> Raw d k -- vertical juxtaposition (diagrammatic composition)
  (::\::)   :: WC Abstractor -> WC (Raw d Noun) -> Raw d Verb
  RVec      :: [WC (Raw Chk Noun)] -> Raw Chk Noun
  RSlice    :: RawSlice -> Raw Chk Noun
  RSelect   :: WC (Raw Syn Noun) -> WC (Raw Chk Noun) -> Raw Chk Noun
  RThin     :: WC (Raw Chk Noun) -> Raw Syn Noun
  RPattern  :: WC (Pattern (WC (Raw Chk Noun))) -> Raw Chk Noun

deriving instance Eq (Raw d k)

instance Show (Raw d k) where
  show (RLet abs xs body)
    = unwords ["let", show abs, "=", show xs, "in", show body]
  show (RNHole name) = '?':name
  show (RVHole name) = '?':name
  show (RSimple tm) = show tm
  show (a ::|:: b) = show a ++ ", " ++ show b
  show (RTh comp) = '{' : show comp ++ "}"
  show (REmb x) = '「' : show x ++ "」"
  show (RPull ps (WC _ (REmb (WC _ (fun ::$:: arg)))))
    = unwords [show fun
              ,"(" ++ concat ((++":") <$> ps)
              ,show arg ++ ")"
              ]
  show (RPull [] x) = "[]:" ++ show x
  show (RPull ps x) = concat ((++":") <$> ps) ++ show x
  show (RVar x) = show x
  show (fun ::$:: arg) = show fun ++ ('(' : show arg ++ ")")
  show (tm ::::: ty) = show tm ++ " :: " ++ show ty
  show (a ::-:: b) = show a ++ "; " ++ show b
  show (xs ::\:: bod) = show xs ++ " -> " ++ show bod
  show (RVec xs) = '[' : intercalate ", " (show <$> xs) ++ "]"
  show (RSlice slice) = '{' : show slice ++ "}slice"
  show (RSelect from slice) = show from ++ ('{' : show slice ++ "}select")
  show (RThin tm) = '~' : show tm
  show (RPattern p) = show p

type Desugar = StateT Namespace (ReaderT RawEnv (Except Error))

instance {-# OVERLAPPING #-} MonadFail Desugar where
  fail = throwError . desugarErr

freshM :: String -> Desugar Name
freshM str = do
  ns <- get
  let (name, ns') = fresh str ns
  put ns'
  pure name

{-
findDuplicates :: Env -> Desugar ()
findDuplicates (ndecls, vdecls, aliases)
  = aux $ concat [(fst &&& show . fst . snd) <$> (unWC <$> ndecls)
                 ,(fst &&& show . fst . snd) <$> (unWC <$> vdecls)
                 ,(fst &&& show . snd) <$> aliases]
 where
  aux :: [(String, String)] -> Desugar ()
  aux xs = case filter ((1<).length) [ filter ((==x).fst) xs | (x,_) <- xs ] of
             []  -> pure () -- all good
             ([]:_) -> undefined -- this should be unreachable
             -- TODO: Include FC
             ((x:xs):_) -> desugarErr . unlines $ (("Multiple definitions of " ++ fst x)
                                                   :(snd <$> (x:xs))
                                                  )
-}

desugarErr :: String -> Error
desugarErr = dumbErr . DesugarErr

desugarVTy :: RawVType -> Desugar VType
desugarVTy (RK ss ts) = K <$> (desugarRow ss) <*> (desugarRow ts)
 where
  desugarSType :: SType' Raw -> Desugar (SType)
  desugarSType (Q q) = pure $ Q q
  desugarSType Bit = pure Bit
  desugarSType (Of sty tm) = Of <$> desugarSType sty <*> desugar' tm
  desugarSType (Rho row) = Rho <$> desugarRow row

  desugarRow :: Row Raw -> Desugar (Row Term)
  desugarRow (R r) = R <$> mapM (traverse desugarSType) r

desugarVTy (RC raw) = C <$> desugarCTy raw
desugarVTy (RSimpleTy simp) = pure $ SimpleTy simp
desugarVTy (RList raw) = List <$> desugarVTy raw
desugarVTy (RProduct raw raw') = Product <$> desugarVTy raw <*> desugarVTy raw'
desugarVTy (RAlias s args) = do
  (_, aliases) <- ask
  case lookup s aliases of
    Nothing -> let msg = DesugarErr $ "Couldn't find an alias for type "
                         ++ unwords (show s:fmap show args)
               in  throwError $ Err Nothing (Just (show s)) msg
    Just (Alias fc _s vars ty) -> do
      unless (length vars == length args)
        (throwError . Err (Just fc) (Just (show s)) . DesugarErr $
          unwords ("Type alias isn't fully applied:":show s:(show <$> args)))
      let concreteTy = foldr (uncurry instantiateVType) ty (zip [0..] args)
      desugarVTy concreteTy
desugarVTy (RTypeFree f) = throwError $
                           desugarErr ("Trying to desugar free type var: " ++ show f)
desugarVTy (RTypeVar x) = throwError $
                          desugarErr ("Trying to desugar bound type var: " ++ show x)
desugarVTy (RVector vty n)
  = Vector <$> desugarVTy vty <*> (unWC <$> desugar n)
desugarVTy (RThinning wee big) = (:<<<:)
                                 <$> (unWC <$> desugar wee)
                                 <*> (unWC <$> desugar big)
desugarVTy (ROption rty) = Option <$> desugarVTy rty

desugarCTy :: CType' RawIO -> Desugar (CType' InOut)
desugarCTy (ss :-> ts) = (:->) <$> desugarIO ss <*> desugarIO ts

desugarIO :: [RawIO] -> Desugar [InOut]
desugarIO = zipWithM aux names
 where
  aux :: String -> RawIO -> Desugar InOut
  aux _ (Named port ty) = (port,) <$> desugarVTy ty
  aux port (Anon ty)    = (port,) <$> desugarVTy ty

desugar :: WC (Raw d k)
        -> Desugar (WC (Term d k))
desugar (WC fc tm)
  = (WC fc <$> desugar' tm)
    `catchError`
    (\(Err _ src msg) -> throwError (Err (Just fc) src msg))

desugar' :: Raw d k
         -> Desugar (Term d k)
-- TODO: holes need to know their arity for type checking
desugar' (RNHole name) = NHole <$> freshM name
desugar' (RVHole name) = VHole <$> freshM name
desugar' (RSimple simp) = pure $ Simple simp
desugar' (a ::|:: b) = (:|:) <$> desugar a <*> desugar b
desugar' (RTh v) = Th <$> desugar v
desugar' (REmb syn) = Emb <$> desugar syn
desugar' (RPull ps raw) = Pull ps <$> desugar raw
desugar' (RVar  name) = pure (Var name)
desugar' (fun ::$:: arg)
  = (:$:) <$> desugar fun <*> desugar arg
desugar' (tm ::::: outputs) = do
  tm <- desugar tm
  ty <- desugarIO outputs
  pure (tm ::: ty)
desugar' (syn ::-:: verb) = (:-:) <$> desugar syn <*> desugar verb
{-
  tys <- nsynth (unWC syn)
  case tys of
    [C (ss :-> ts)] -> do l <- desugar syn
                          r <- desugar verb
                          pure (l :-: r)
-}
desugar' (abst ::\:: raw) = (abst :\:) <$> desugar raw
desugar' (RVec raws)
  = Vec <$> mapM (\tm -> desugar tm) raws
desugar' (RPattern x) = Pattern <$> traverse desugarPattern x
 where
  desugarPattern :: Pattern (WC (Raw Chk Noun)) -> Desugar (Pattern (WC (Term Chk Noun)))
  desugarPattern p = traverse (traverse desugar') p
desugar' (RLet abs thing body) = Let abs <$> desugar thing <*> desugar body
desugar' x = throwError . desugarErr $ "desugar'"  ++ show x

desugarNClause :: Clause Raw Noun -> Desugar (Clause Term Noun)
desugarNClause (ThunkOf clause) = ThunkOf <$> traverse desugarVClause clause
desugarNClause (NoLhs body) = NoLhs <$> desugar body
desugarNClause Undefined = pure Undefined

desugarVClause :: Clause Raw Verb -> Desugar (Clause Term Verb)
desugarVClause (Clauses cs) = Clauses <$> mapM branch cs
 where
  branch :: (WC Abstractor, WC (Raw Chk Noun)) -> Desugar (WC Abstractor, WC (Term Chk Noun))
  branch (lhs, rhs) = (lhs,) <$> desugar rhs
desugarVClause (NoLhs rhs) = NoLhs <$> desugar rhs
desugarVClause Undefined = pure Undefined

desugarDecl :: RawDecl -> Desugar Decl
desugarDecl d@Decl{..} = do
  tys  <- desugarIO fnSig
  noun <- {- fmap bindTerm <$> -} desugarNClause fnBody
  pure $ d { fnBody = noun
           , fnSig  = tys
           }

desugarEnv :: RawEnv -> Either Error [Decl]
desugarEnv env@(decls, _)
  = fmap fst
    . runExcept
    . flip runReaderT env
    . flip runStateT root
    $ mapM desugarDecl decls

abstractVType :: UserName -> Int -> RawVType -> RawVType
abstractVType x n (RC ctype) = RC (fmap (abstractVType x n) <$> ctype)
-- All of our simple types are first order for now
abstractVType _ _ ty@(RSimpleTy _) = ty
abstractVType x n (RList ty) = RList (abstractVType x n ty)
abstractVType x n (RProduct a b) = RProduct
                                     (abstractVType x n a)
                                     (abstractVType x n b)
abstractVType x n (RAlias name args) = RAlias name (abstractVType x n <$> args)
abstractVType x n free@(RTypeFree y) | x == y = RTypeVar n
                                     | otherwise = free
abstractVType _ _ ty@(RTypeVar _) = ty
abstractVType x n (RVector ty size) = RVector (abstractVType x n ty) size
abstractVType _ _ (RThinning a b) = RThinning a b
abstractVType _ _ (RK r r') = RK r r'
abstractVType _ _ (ROption ty) = ROption ty

instantiateVType :: Int -> RawVType -> RawVType -> RawVType
instantiateVType n to (RC ctype) = RC (fmap (instantiateVType n to) <$> ctype)
instantiateVType _ _  ty@(RSimpleTy _) = ty
instantiateVType n to (RList ty) = RList (instantiateVType n to ty)
instantiateVType n to (RProduct a b) = RProduct
                                       (instantiateVType n to a)
                                       (instantiateVType n to b)
instantiateVType n to (RAlias name args) = RAlias name (instantiateVType n to <$> args)
instantiateVType _ _  ty@(RTypeFree _) = ty
instantiateVType n to ty@(RTypeVar m) | n == m = to
                                      | otherwise = ty
instantiateVType n to (RVector ty m) = RVector (instantiateVType n to ty) m
instantiateVType _ _  (RThinning a b) = RThinning a b
instantiateVType _ _ (RK r r') = RK r r'
instantiateVType n to (ROption ty) = ROption $ instantiateVType n to ty

{-
abstractTerm :: Abstractor -> Term d k -> Term d k
abstractTerm abst tm = let bindings = zip (aux abst) [0..]
                       in  foldr nameTo tm bindings
 where
  aux :: Abstractor -> [String]
  aux (Bind x) = [x]
  aux (x :||: y) = aux x ++ aux y
  -- Port pulling here is referring to the arguments, so doesn't affect us
  aux (APull _ x) = aux x

  len :: Abstractor -> Int
  len (Bind _) = 1
  len (x :||: y) = len x + len y
  len (APull _ x) = len x

  nameTo :: (String, Int) -> Term d k -> Term d k
  nameTo (x, n) (Var y) | x == y = Bound n
                        | otherwise = Var y
  nameTo xn (a :|: b) = (nameTo xn <$> a) :|: (nameTo xn <$> b)
  nameTo xn (Th f) = Th (nameTo xn <$> f)
  nameTo xn (Emb y) = Emb (nameTo xn <$> y)
  nameTo _ (Pull _ _) = undefined -- hmm
  nameTo xn (fun :$: arg) = (nameTo xn <$> fun) :$: (nameTo xn <$> arg)
  nameTo xn (tm ::: ty) = (nameTo xn <$> tm) ::: ty
  nameTo xn (Do f) = Do $ nameTo xn <$> f
  nameTo xn (a :-: b) = (nameTo xn <$> a) :-: (nameTo xn <$> b)
  nameTo (x, n) (abst :\: body) = abst :\: (nameTo (x, n + len (unWC abst)) <$> body)
  nameTo xn (Vec xs) = Vec (fmap (nameTo xn) <$> xs)
  nameTo xn (Select from th) = Select (nameTo xn <$> from) (nameTo xn <$> th)
  nameTo xn (Slice size slice) = Slice (nameTo xn <$> size) (fmap (nameTo xn) <$> slice)
  nameTo _ tm = tm

bindTerm :: Term d k -> Term d k
bindTerm (a :|: b) = (bindTerm <$> a) :|: (bindTerm <$> b)
bindTerm (Th f) = Th (bindTerm <$> f)
bindTerm (Emb x) = Emb (bindTerm <$> x)
bindTerm (Pull _ _) = undefined -- hmm
bindTerm (fun :$: arg) = (bindTerm <$> fun) :$: (bindTerm <$> arg)
bindTerm (tm ::: ty) = (bindTerm <$> tm) ::: ty
bindTerm (Do f) = Do $ bindTerm <$> f
bindTerm (a :-: b) = (bindTerm <$> a) :-: (bindTerm <$> b)
bindTerm (abst :\: body) = abst :\: (abstractTerm (unWC abst) <$> body)
bindTerm (Vec xs) = Vec (fmap bindTerm <$> xs)
bindTerm (Select from th) = Select (bindTerm <$> from) (bindTerm <$> th)
bindTerm (Slice size slice) = Slice (bindTerm <$> size) (fmap bindTerm <$> slice)
bindTerm x = x
-}
