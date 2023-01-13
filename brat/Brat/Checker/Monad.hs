{-# LANGUAGE FlexibleContexts #-}

module Brat.Checker.Monad where

import Brat.Checker.Quantity (Quantity(..), qpred)
import Brat.Checker.Types
import Brat.Constructors (ConstructorMap)
import Brat.Error (Error(..), ErrorMsg(..), dumbErr)
import Brat.Eval
import Brat.FC
import Brat.Graph
import Brat.Naming (fresh, Name, Namespace)
import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.UserName (UserName)
import Bwd
import Util

import Control.Monad.Freer

import Control.Applicative (liftA2)
import Control.Monad.Fail ()
import Data.Foldable (traverse_)
import Data.Functor (($>))
import Data.List (intercalate)
import qualified Data.Map as M

data Context = Ctx { venv   :: VEnv
                   , store  :: Store
                   , constructors :: ConstructorMap
                   , typeConstructors :: M.Map UserName TypeKind
                   , aliasTable :: M.Map UserName ([(PortName, TypeKind)], [ValPat], Value)
                   }

data CheckingSig ty where
  Fresh   :: String -> CheckingSig Name
  Throw   :: Error  -> CheckingSig a
  LogHole :: TypedHole -> CheckingSig ()
  AskFC   :: CheckingSig FC
  VLup    :: UserName -> CheckingSig (Maybe [(Src, BinderType Brat)])
  KLup    :: UserName -> CheckingSig (Maybe (Src, BinderType Kernel))
  -- Lookup type constructors
  TLup    :: TypeKind -> UserName -> CheckingSig (Maybe [(PortName, TypeKind)])
  -- Lookup term constructor - ask whether a constructor builds a certain type
  CLup    :: UserName -- Value constructor
          -> UserName  -- Type constructor
          -> CheckingSig ([ValPat]
                         ,[(PortName, BinderType Brat)])
  -- Lookup an end in the Store
  ELup    :: End -> CheckingSig (Maybe Value)
  -- Lookup an alias in the table
  ALup    :: UserName -> CheckingSig (Maybe ([(PortName, TypeKind)], [ValPat], Value))
  EndKind :: End -> CheckingSig (Maybe TypeKind)
  AddNode :: Name -> Node -> CheckingSig ()
  Wire    :: Wire -> CheckingSig ()
  KDone   :: CheckingSig ()
  AskVEnv :: CheckingSig VEnv
  Declare :: End -> TypeKind -> CheckingSig ()
  Define  :: End -> Value -> CheckingSig ()

localAlias :: (UserName, [(PortName, TypeKind)], [ValPat], Value) -> Checking v -> Checking v
localAlias _ (Ret v) = Ret v
localAlias con@(name, args, pats, val) (Req (ALup u) k)
  | u == name = localAlias con $ k (Just (args, pats, val))
localAlias con (Req r k) = Req r (localAlias con . k)

localFC :: FC -> Checking v -> Checking v
localFC _ (Ret v) = Ret v
localFC f (Req AskFC k) = localFC f (k f)
localFC f (Req (Throw (e@Err{fc=Nothing})) k) = localFC f (Req (Throw (e{fc=Just f})) k)
localFC f (Req r k) = Req r (localFC f . k)

localEnv :: (?my :: Modey m) => Env (EnvData m) -> Checking v -> Checking v
localEnv = case ?my of
  Braty -> localVEnv
  Kerny -> \env m -> localKVar env (m <* req KDone)

localVEnv :: VEnv -> Checking v -> Checking v
localVEnv _   (Ret v) = Ret v
localVEnv ext (Req (VLup x) k) | Just x <- M.lookup x ext = localVEnv ext (k (Just x))
localVEnv ext (Req AskVEnv k) = do env <- req AskVEnv
                                   localVEnv ext (k (M.union ext env)) -- ext shadows env
localVEnv ext (Req r k) = Req r (localVEnv ext . k)

wrapError :: (Error -> Error) -> Checking v -> Checking v
wrapError _ (Ret v) = Ret v
wrapError f (Req (Throw e) k) = Req (Throw (f e)) k
wrapError f (Req r k) = Req r (wrapError f . k)

throwLeft :: Either ErrorMsg a -> Checking a
throwLeft (Right x) = pure x
throwLeft (Left msg) = err msg

vlup :: UserName -> Checking [(Src, BinderType Brat)]
vlup s = do
  req (VLup s) >>= \case
    Just vty -> pure vty
    Nothing -> err $ VarNotFound (show s)

alup :: UserName -> Checking ([(PortName, TypeKind)], [ValPat], Value)
alup s = do
  req (ALup s) >>= \case
    Just vty -> pure vty
    Nothing -> err $ VarNotFound (show s)

lookupAndUse :: UserName -> KEnv
             -> Either Error (Maybe ((Src, BinderType Kernel), KEnv))
lookupAndUse x kenv = case M.lookup x kenv of
   Nothing -> Right Nothing
   Just (q, rest) -> case qpred q of
                      Nothing -> Left $ dumbErr $ TypeErr $ (show x) ++ " has already been used"
                      Just q -> Right $ Just (rest, M.insert x (q, rest) kenv)

localKVar :: KEnv -> Checking v -> Checking v
localKVar _   (Ret v) = Ret v
localKVar env (Req (KLup x) k) = case lookupAndUse x env of
                                   Left err@(Err (Just _) _) -> req $ Throw err
                                   Left (Err Nothing msg) -> err msg
                                   Right (Just (th, env)) -> localKVar env (k (Just th))
                                   Right Nothing -> Req (KLup x) (localKVar env . k)
localKVar env (Req KDone k) = case [ x | (x,(One,_)) <- M.assocs env ] of
                                [] -> (localKVar env . k) ()
                                xs -> typeErr $
                                      unwords ["Variable(s)"
                                              ,intercalate ", " (fmap show xs)
                                              ,"haven't been used"
                                              ]
localKVar env (Req r k) = Req r (localKVar env . k)

catchErr :: Free CheckingSig a -> Free CheckingSig (Either Error a)
catchErr (Ret t) = Ret (Right t)
catchErr (Req (Throw e) _) = pure $ Left e
catchErr (Req r k) = Req r (catchErr . k)

handler :: Free CheckingSig v
        -> Context
        -> Namespace
        -> Either Error (v,([TypedHole],Graph),Namespace)
handler (Ret v) _ ns = return (v, mempty, ns)
handler (Req s k) ctx ns
  = case s of
      Fresh str -> let (name, root) = fresh str ns in
                     handler (k name) ctx root
      Throw err -> Left err
      LogHole hole -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                         return (v,(hole:holes,g),ns)
      AskFC -> error "AskFC in handler - shouldn't happen, should always be in localFC"
      VLup s -> handler (k $ M.lookup s (venv ctx)) ctx ns
      ALup s -> handler (k $ M.lookup s (aliasTable ctx)) ctx ns
      AddNode name node -> do
        (v,(holes,g),ns) <- handler (k ()) ctx ns
        return (v,(holes,(M.singleton name node, []) <> g),ns)
      Wire w -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                   return (v,(holes,(M.empty,[w]) <> g),ns)
      -- We only get a KLup here if the variable has not been found in the kernel context
      KLup _ -> handler (k Nothing) ctx ns
      -- Receiving KDone may become possible when merging the two check functions
      KDone -> error "KDone in handler - this shouldn't happen"
      AskVEnv -> handler (k (venv ctx)) ctx ns
      ELup end -> handler (k ((M.lookup end) . valueMap . store $ ctx)) ctx ns
      EndKind end -> handler (k ((M.lookup end) . kindMap . store $ ctx)) ctx ns
      Declare end kind ->
        let st@Store{kindMap=m} = store ctx
        in case M.lookup end m of
          Just _ -> Left $ dumbErr (InternalError $ "Redeclaring " ++ show end)
          Nothing -> handler (k ())
            (ctx { store =
              st { kindMap = M.insert end kind m }
            }) ns
      Define end v ->
        let st@Store{kindMap=km, valueMap=vm} = store ctx
        in case M.lookup end vm of
          Just _ -> Left $ dumbErr (InternalError $ "Redefining " ++ show end)
          Nothing -> case M.lookup end km of
            Nothing -> Left $ dumbErr (InternalError $ "Defining un-Declared " ++ show end)
            Just _ -> -- TODO can we check the value is of the kind declared?
              handler (k ())
                (ctx { store =
                    st { valueMap = M.insert end v vm }
                }) ns
      -- TODO: Use the kind argument for partially applied constructors
      TLup _ c -> do
        args <- case M.lookup c (typeConstructors ctx) of
          Just (Star args) -> pure $ Just args
          Just Nat -> error "Nat type constructor - this shouldn't happen"
          Nothing -> pure Nothing
        handler (k args) ctx ns

      CLup vcon tycon -> do
        tbl <- maybeToRight (dumbErr $ VConNotFound $ show vcon) $
               M.lookup vcon (constructors ctx)
        args <- maybeToRight (dumbErr $ TyConNotFound (show tycon) (show vcon)) $
                M.lookup tycon tbl
        handler (k args) ctx ns

type Checking = Free CheckingSig

instance Semigroup a => Semigroup (Checking a) where
  (<>) = liftA2 (<>)

instance Monoid a => Monoid (Checking a) where
  mempty = pure mempty
  mappend = liftA2 mappend

err :: ErrorMsg -> Checking a
err msg = do
  fc <- req AskFC
  req $ Throw $ Err (Just fc) msg

typeErr :: String -> Checking a
typeErr = err . TypeErr

-- This way we get file contexts when pattern matching fails
instance MonadFail Checking where
  fail = typeErr

kindEq :: TypeKind -> TypeKind -> Either ErrorMsg ()
kindEq Nat Nat = Right ()
kindEq (Star xs) (Star ys) = kindListEq xs ys
 where
  kindListEq :: [(PortName, TypeKind)] -> [(PortName, TypeKind)] -> Either ErrorMsg ()
  kindListEq [] [] = Right ()
  kindListEq ((_, x):xs) ((_, y):ys) = kindEq x y *> kindListEq xs ys
  kindListEq _ _ = Left $ TypeErr "Unequal kind lists"
kindEq _ _ = Left $ TypeErr "Unequal kinds"

-- The first arg is the term we're querying for error reporting
-- Expected type, then actual type
typeEq :: String -> TypeKind
       -> Value -- Expected
       -> Value -- Actual
       -> Checking ()
typeEq tm k s t = do
  s <- evTy s
  t <- evTy t
  eq 0 k s t
 where
  -- All of these functions assume that normalisation has already happened
  -- Int arg is the next de Bruijn level
  eq :: Int -> TypeKind
     -> Value -- Expected
     -> Value -- Actual
     -> Checking ()
  eq _ Nat (VNum n) (VNum m) | n == m = pure ()
  eq _ Nat (VApp v B0) (VApp v' B0)
   | v == v' = kindOf v >>= \k -> throwLeft (kindEq Nat k) $> ()
  eq l (Star ((_, k):ks)) f g = do
   let x = varVal k (VLvl l k)
   f <- apply (req . ELup) f x
   g <- apply (req . ELup) g x
   eq (l + 1) (Star ks) f g
  eq l (Star []) (VCon c vs) (VCon c' vs') | c == c' = do
    req (TLup (Star []) c) >>= \case
      Just ks -> eqs l (snd <$> ks) vs vs'
      Nothing -> typeErr $ "Type constructor " ++ show c ++ " undefined"
  eq l k@(Star []) (VApp v ss) (VApp v' ss') | v == v' = do
    kindOf v >>= \case
      Star ks -> eqs l (snd <$> ks) (ss <>> []) (ss' <>> [])
      k' -> err (KindMismatch (show tm) (show k) (show k'))
  eq l (Star []) (VFun Braty _ cty) (VFun Braty _ cty')
    = eqCType l Braty cty cty'
  eq l (Star []) (VFun Kerny _ cty) (VFun Kerny _ cty')
    = eqCType l Kerny cty cty'
  eq _ _ s t = err $ TypeMismatch tm (show s) (show t)

  kindOf :: VVar -> Checking TypeKind
  kindOf (VLvl _ k) = pure k
  kindOf (VPar e) = req (EndKind e) >>= \case
    Just k -> pure k
    Nothing -> typeErr "Kind not found"
  kindOf (VInx _) = error "kindOf used on de Bruijn index"

  eqs :: Int -> [TypeKind] -> [Value] -> [Value] -> Checking ()
  eqs _ [] [] [] = pure ()
  eqs l (k:ks) (u:us) (v:vs) = eq l k u v *> eqs l ks us vs
  eqs _ _ us vs = typeErr $ "Arity mismatch in type constructor arguments:\n  "
              ++ show us ++ "\n  " ++ show vs

  eqCType :: Show (BinderType m)
          => Int -> Modey m -> CType' (PortName, BinderType m)
          -> CType' (PortName, BinderType m) -> Checking ()
  eqCType l m (ss :-> ts) (ss' :-> ts') = do
    acc <- eqRow m (B0, l) ss ss'
    eqRow m acc ts ts'
    pure ()

  eqRow :: Show (BinderType m)
        => Modey m
        -> (Bwd (Int, TypeKind), Int)
        -> [(PortName, BinderType m)] -> [(PortName, BinderType m)]
        -> Checking (Bwd (Int, TypeKind), Int)
  eqRow _ acc [] [] = pure acc
  eqRow Braty (lvls, l) ((_, Left k):ks) ((_, Left k'):ks') = do
    throwLeft $ kindEq k k'
    eqRow Braty (lvls :< (l, k), l + 1) ks ks'
  eqRow Braty acc@(lvls, l) ((_, Right t):ks) ((_, Right t'):ks') = do
    eq l (Star []) (changeVar (InxToLvl lvls) 0 t) (changeVar (InxToLvl lvls) 0 t')
    eqRow Braty acc ks ks'
  eqRow Kerny acc ((_, t):ts) ((_, t'):ts') = stypeEq tm t t' *> eqRow Kerny acc ts ts'
  eqRow _ _ (t:_) (t':_) = err $ TypeMismatch (show tm) (show t) (show t')
  eqRow _ _ ss [] = typeErr $ "eqRow: Ragged rows " ++ show ss ++ " and []"
  eqRow _ _ [] ts = typeErr $ "eqRow: Ragged rows [] and " ++ show ts

stypeEq :: String -> SValue -> SValue -> Checking ()
stypeEq tm (Of sty n) (Of sty' n') = do
  typeEq tm Nat n n'
  stypeEq tm sty sty'
stypeEq _ (Q q) (Q q') | q == q' = pure ()
stypeEq _ Bit Bit = pure ()
stypeEq tm (Rho (R row)) (Rho (R row'))
  = traverse_ (uncurry (stypeEq tm)) (zip (snd <$> row) (snd <$> row'))
stypeEq tm t t' = err $ TypeMismatch tm (show t) (show t')

evTy :: Value -> Checking Value
evTy = eval (req . ELup) B0

evVa :: Value -> Checking Value
evVa = eval (req . ELup) B0

evSTy :: SValue -> Checking SValue
evSTy = eval (req . ELup) B0
