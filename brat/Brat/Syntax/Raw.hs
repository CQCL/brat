{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
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

type family TypeOf (k :: Kind) :: Type where
  TypeOf Noun = [InOut]
  TypeOf Verb = CType

data RawVType
  = RC RawCType
  | RSimpleTy SimpleType
  | RList RawVType
  | RProduct RawVType RawVType
  | RAlias String [RawVType]
  | RTypeFree String
  | RTypeVar Int
  | RVector RawVType (WC (Raw Chk Noun))
  | RThinning (WC (Raw Chk Noun)) (WC (Raw Chk Noun))
  | RK (Row Raw Quantum) (Row Raw Quantum)
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

data TypeAlias = Alias FC String [String] RawVType deriving (Eq, Show)

type RawNDecl = NDecl' RawIO Raw
type RawVDecl = VDecl' RawIO Raw
type Env = ([RawNDecl], [RawVDecl], [(String, TypeAlias)])

type RawSlice = Slice (WC (Raw Chk Noun))

data Raw :: Dir -> Kind -> Type where
  -- not sure about this
  RLet      :: WC (Raw Chk k) -> WC (Raw d k) -> Raw d k
  RNHole    :: String -> Raw Chk Noun
  RVHole    :: String -> Raw Chk Verb
  RSimple   :: SimpleTerm -> Raw Chk Noun
  RPair     :: WC (Raw Chk Noun) -> WC (Raw Chk Noun) -> Raw Chk Noun
  (::|::)   :: WC (Raw d k) -> WC (Raw d k) -> Raw d k
  RTh       :: WC (Raw Chk Verb) -> Raw Chk Noun
  REmb      :: WC (Raw Syn k) -> Raw Chk k
  RPull     :: [Port] -> WC (Raw Chk k) -> Raw Chk k
  RVar      :: String -> Raw Syn Noun
  (::$::)   :: WC (Raw Syn Noun) -> WC (Raw Chk Noun) -> Raw Syn Noun -- Eval with ChkRaw n argument
  (:::::)   :: WC (Raw Chk k) -> [RawIO] -> Raw Syn k
  RDo       :: WC (Raw Syn Noun) -> Raw Syn Verb
  (::-::)   :: WC (Raw Syn k) -> WC (Raw d Verb) -> Raw d k -- vertical juxtaposition (diagrammatic composition)
  (::\::)   :: WC Abstractor -> WC (Raw d Noun) -> Raw d Verb
  RVec      :: [WC (Raw Chk Noun)] -> Raw Chk Noun
  RSlice    :: RawSlice -> Raw Chk Noun
  RSelect   :: WC (Raw Syn Noun) -> WC (Raw Chk Noun) -> Raw Chk Noun
  RThin     :: WC (Raw Chk Noun) -> Raw Syn Noun
  RPattern  :: WC (Pattern (WC (Raw Chk Noun))) -> Raw Chk Noun

deriving instance Eq (Raw d k)

instance Show (Raw d k) where
  show (RLet _ _) = undefined
  show (RNHole name) = '?':name
  show (RVHole name) = '?':name
  show (RSimple tm) = show tm
  show (RPair a b) = '[': show a ++ ", " ++ show b ++  "]"
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
  show (RVar x) = x
  show (fun ::$:: arg) = show fun ++ ('(' : show arg ++ ")")
  show (tm ::::: ty) = show tm ++ " :: " ++ show ty
  show (RDo f) = show f ++ "!"
  show (a ::-:: b) = show a ++ "; " ++ show b
  show (xs ::\:: bod) = show xs ++ " -> " ++ show bod
  show (RVec xs) = '[' : intercalate ", " (show <$> xs) ++ "]"
  show (RSlice slice) = '{' : show slice ++ "}slice"
  show (RSelect from slice) = show from ++ ('{' : show slice ++ "}select")
  show (RThin tm) = '~' : show tm
  show (RPattern p) = show p

type Desugar = StateT Namespace (ReaderT Env (Except Error))

instance {-# OVERLAPPING #-} MonadFail Desugar where
  fail = dumbErr

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
             ((x:xs):_) -> dumbErr . unlines $ (("Multiple definitions of " ++ fst x)
                                                :(snd <$> (x:xs))
                                               )
-}

dumbErr :: String -> Desugar a
dumbErr = throwError . Err Nothing Nothing . DesugarErr

desugarVTy :: RawVType -> Desugar VType
desugarVTy (RK ss ts) = K <$> (desugarRow ss) <*> (desugarRow ts)
 where
  desugarSType :: SType Raw -> Desugar (SType Term)
  desugarSType (Q q) = pure $ Q q
  desugarSType Bit = pure Bit
  desugarSType (Of sty tm) = Of <$> desugarSType sty <*> desugar' tm
  desugarSType (Rho row) = Rho <$> desugarRow row

  desugarRow :: Row Raw Quantum -> Desugar (Row Term Quantum)
  desugarRow (R r) = R <$> mapM (traverse desugarSType) r

desugarVTy (RC raw) = C <$> desugarCTy raw
desugarVTy (RSimpleTy simp) = pure $ SimpleTy simp
desugarVTy (RList raw) = List <$> desugarVTy raw
desugarVTy (RProduct raw raw') = Product <$> desugarVTy raw <*> desugarVTy raw'
desugarVTy (RAlias s args) = do
  (_, _, aliases) <- ask
  case lookup s aliases of
    Nothing -> let msg = DesugarErr $ "Couldn't find an alias for type " ++ unwords (s:fmap show args)
               in  throwError $ Err Nothing (Just s) msg
    Just (Alias fc _ vars ty) -> do
      unless (length vars == length args)
        (throwError . Err (Just fc) (Just s) . DesugarErr $
          unwords ("Type alias isn't fully applied:":s:(show <$> args)))
      let concreteTy = foldr (uncurry instantiateVType) ty (zip [0..] args)
      desugarVTy concreteTy
desugarVTy (RTypeFree f) = dumbErr ("Trying to desugar free type var: " ++ f)
desugarVTy (RTypeVar x) = dumbErr ("Trying to desugar bound type var: " ++ show x)
desugarVTy (RVector vty n)
  = Vector <$> desugarVTy vty <*> (unWC <$> desugar n)
desugarVTy (RThinning wee big) = (:<<<:)
                                 <$> (unWC <$> desugar wee)
                                 <*> (unWC <$> desugar big)
desugarVTy (ROption rty) = Option <$> desugarVTy rty

desugarCTy :: CType' RawIO -> Desugar (CType' InOut)
desugarCTy (ss :-> ts) = (:->) <$> desugarIO ss <*> desugarIO ts

desugarIO :: [RawIO] -> Desugar [InOut]
desugarIO = zipWithM aux [0..]
 where
  aux :: Int -> RawIO -> Desugar InOut
  aux _ (Named port ty) = (port,) <$> desugarVTy ty
  aux i (Anon ty) = ('_':show i,) <$> desugarVTy ty

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
desugar' (RPair a b) = Pair <$> desugar a <*> desugar b
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
desugar' (RDo noun) = Do <$> desugar noun
desugar' tm@(syn ::-:: verb) = (:-:) <$> desugar syn <*> desugar verb
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
desugar' x = dumbErr $ "desugar'"  ++ show x
{-
nsynth :: Raw Syn Noun -> Desugar [VType]
nsynth (RLet _ _) = undefined
nsynth (l ::|:: r) = (++) <$> nsynth (unWC l) <*> nsynth (unWC r)
nsynth (RVar name) = do (venv, _, _) <- ask
                           let (Just ty) = lookupBy ((==name).fnName) fnSig venv
                           io <- desugarIO ty
                           pure (snd <$> io)
nsynth (fun ::$:: _) = do [C (_ :-> ts)] <- nsynth (unWC fun)
                          pure (snd <$> ts)
nsynth (_ ::::: ty) = fmap snd <$> desugarIO ty
nsynth (_ ::-:: bot) = do (_ :-> ts) <- vsynth (unWC bot)
                          pure (snd <$> ts)
nsynth t@(RThin _) = throwError $ Err Nothing Nothing (Unimplemented "nsynth" [show t])

vsynth :: Raw Syn Verb -> Desugar CType
vsynth t@(RLet _ _) = throwError $ Err Nothing Nothing (Unimplemented "vsynth" [show t])
vsynth (l ::|:: r)  = do (ss :-> ts) <- vsynth (unWC l)
                         (us :-> vs) <- vsynth (unWC r)
                         pure $ (ss ++ us) :-> (ts ++ vs)
vsynth (_ ::::: ty) = ([] :-> ) <$> desugarIO ty
vsynth (RDo n) = do [C cty] <- nsynth (unWC n)
                    pure cty
vsynth (top ::-:: bot) = do (ss :-> _ ) <- vsynth (unWC top)
                            (_  :-> ts) <- vsynth (unWC bot)
                            pure (ss :-> ts)
vsynth (_ ::\:: body) = do [C cty] <- nsynth (unWC body)
                           pure cty
-}

desugarNClause :: Clause Raw Noun -> Desugar (Clause Term Noun)
desugarNClause (NounBody body) = NounBody <$> desugar body
desugarNClause Undefined = pure Undefined

desugarVClause :: Clause Raw Verb -> Desugar (Clause Term Verb)
desugarVClause (Clauses cs) = Clauses <$> mapM branch cs
 where
  branch :: (WC Abstractor, WC (Raw Chk Noun)) -> Desugar (WC Abstractor, WC (Term Chk Noun))
  branch (lhs, rhs) = (lhs,) <$> desugar rhs
desugarVClause (NoLhs rhs) = NoLhs <$> desugar rhs
desugarVClause Undefined = pure Undefined

desugarNDecl :: RawNDecl -> Desugar NDecl
desugarNDecl d@Decl{..} = do
  tys  <- desugarIO fnSig
  noun <- {- fmap bindTerm <$> -} desugarNClause fnBody
  pure $ d { fnBody = noun
           , fnSig  = tys
           }

desugarVDecl :: RawVDecl -> Desugar VDecl
desugarVDecl d@Decl{..} = do
  cty <- desugarCTy fnSig
  verb <- {- fmap bindTerm <$> -} desugarVClause fnBody
  pure $ d { fnBody = verb
           , fnSig  = cty
           }

desugarEnv :: Env -> Either Error ([NDecl], [VDecl])
desugarEnv env@(ndecls, vdecls, _)
  = fmap fst
    . runExcept
    . flip runReaderT env
    . flip runStateT root
    $ do --findDuplicates env
         ndecls <- mapM desugarNDecl ndecls
         vdecls <- mapM desugarVDecl vdecls
         pure (ndecls, vdecls)

abstractVType :: String -> Int -> RawVType -> RawVType
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
abstractVType x n (RK r r') = RK r r'

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
instantiateVType n to (RK r r') = RK r r'

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
  nameTo xn (Pair a b) = Pair (nameTo xn <$> a) (nameTo xn <$> b)
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
bindTerm (Pair a b) = Pair (bindTerm <$> a) (bindTerm <$> b)
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
