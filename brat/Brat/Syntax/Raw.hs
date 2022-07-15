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

class Desugarable ty where
  type Desugared ty
  desugar :: WC ty -> Desugar (WC (Desugared ty))
  desugar (WC fc tm)
    = (WC fc <$> desugar' tm)
      `catchError`
      (\(Err _ src msg) -> throwError (Err (Just fc) src msg))

  desugar' :: ty -> Desugar (Desugared ty)

instance Desugarable (SType' Raw) where
  type Desugared (SType' Raw) = SType
  desugar' (Q q) = pure $ Q q
  desugar' Bit = pure Bit
  desugar' (Of sty tm) = Of <$> desugar' sty <*> desugar' tm
  desugar' (Rho row) = Rho <$> desugar' row

instance Desugarable (Row Raw) where
  type Desugared (Row Raw) = Row Term
  desugar' (R r) = R <$> mapM (traverse desugar') r

instance Desugarable RawVType where
  type Desugared RawVType = VType
  desugar' (RK ss ts) = K <$> (desugar' ss) <*> (desugar' ts)
  desugar' (RC raw) = C <$> desugar' raw
  desugar' (RSimpleTy simp) = pure $ SimpleTy simp
  desugar' (RList raw) = List <$> desugar' raw
  desugar' (RProduct raw raw') = Product <$> desugar' raw <*> desugar' raw'
  desugar' (RAlias s args) = do
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
        desugar' concreteTy
  desugar' (RTypeFree f) = throwError $
                             desugarErr ("Trying to desugar free type var: " ++ show f)
  desugar' (RTypeVar x) = throwError $
                            desugarErr ("Trying to desugar bound type var: " ++ show x)
  desugar' (RVector vty n)
    = Vector <$> desugar' vty <*> (unWC <$> desugar n)
  desugar' (RThinning wee big) = (:<<<:)
                                   <$> (unWC <$> desugar wee)
                                   <*> (unWC <$> desugar big)
  desugar' (ROption rty) = Option <$> desugar' rty

instance Desugarable (CType' RawIO) where
  type Desugared (CType' RawIO) = CType' InOut
  desugar' (ss :-> ts) = (:->) <$> desugar' ss <*> desugar' ts

instance Desugarable [RawIO] where
  type Desugared [RawIO] = [InOut]
  desugar' = zipWithM aux names
   where
    aux :: String -> RawIO -> Desugar InOut
    aux _ (Named port ty) = (port,) <$> desugar' ty
    aux port (Anon ty)    = (port,) <$> desugar' ty

instance Desugarable (Raw d k) where
  type Desugared (Raw d k) = Term d k
  -- TODO: holes need to know their arity for type checking
  desugar' (RNHole name) = NHole <$> freshM name
  desugar' (RVHole name) = VHole <$> freshM name
  desugar' (RSimple simp) = pure $ Simple simp
  desugar' (a ::|:: b) = (:|:) <$> desugar a <*> desugar b
  desugar' (RTh v) = Th <$> desugar v
  desugar' (REmb syn) = Emb <$> desugar syn
  desugar' (RPull ps raw) = Pull ps <$> desugar raw
  desugar' (RVar  name) = pure (Var name)
  desugar' (fun ::$:: arg) = (:$:) <$> desugar fun <*> desugar arg
  desugar' (tm ::::: outputs) = do
    tm <- desugar tm
    ty <- desugar' outputs
    pure (tm ::: ty)
  desugar' (syn ::-:: verb) = (:-:) <$> desugar syn <*> desugar verb
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

instance Desugarable RawDecl where
  type Desugared RawDecl = Decl
  desugar' d@Decl{..} = do
    tys  <- desugar' fnSig
    noun <- desugarNClause fnBody
    pure $ d { fnBody = noun
             , fnSig  = tys
             }

desugarEnv :: RawEnv -> Either Error [Decl]
desugarEnv env@(decls, _)
  = fmap fst
    . runExcept
    . flip runReaderT env
    . flip runStateT root
    $ mapM desugar' decls

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
