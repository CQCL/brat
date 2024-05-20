{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}

module Brat.Eval (Eval(..)
                 ,EvMode(..)
                 ,ValPat(..)
                 ,NumPat(..)
                 ,apply
                 ,eqTest
                 ,eqRowTest
                 ,kindEq
                 ,kindType
                 ,numVal
                 ,typeEq
                 ,standardise
                 ) where

import Brat.Checker.Monad
import Brat.Checker.Types (EndType(..))
import Brat.Error (ErrorMsg(..))
import Brat.Syntax.Value
import Brat.Syntax.Common
import Brat.UserName (plain)
import Control.Monad.Freer (req)
import Bwd
import Hasochism (N(..), Flip(..), Some(..))

import Control.Monad (zipWithM)
import Data.Bifunctor (bimap)
import Data.Functor
import Data.Kind (Type)
import Data.Type.Equality (TestEquality(..), (:~:)(..))

kindType :: TypeKind -> Val Z
kindType Nat = TNat
kindType (TypeFor _ []) = VCon (plain "nil") []
kindType (TypeFor m ks)
  = VFun Braty $ helper ks :->> (RPr ("type", kindType (TypeFor m [])) R0)
 where
  helper :: [(PortName, TypeKind)] -> Ro Brat Z Z
  helper [] = R0
  helper ((p,k):ks) = RPr (p,kindType k) (helper ks)

-- It's very difficult to call methods from this typeclass without using type
-- applications (i.e. mEval @Brat) because all uses of m are arguments to type
-- families, so cannot be inferred from constraints
class MODEY m => EvMode m where
  tyBinder :: Val Z -> BinderType m
  mEval :: Valz n -> Val n -> Checking (Val Z)
  biType :: BinderType m -> Val Z

instance EvMode Brat where
  tyBinder = Right
  mEval = eval
  biType = either kindType id

instance EvMode Kernel where
  tyBinder = id
  mEval = eval
  biType = id

evModily :: Modey m -> (EvMode m => t) -> t
evModily Braty t = t
evModily Kerny t = t

-- Put things into a standard form in a kind-directed manner, such that it is
-- meaningful to do case analysis on them
standardise :: TypeKind -> Val Z -> Checking (Val Z)
standardise k val = eval S0 val <&> (k,) >>= \case
  (Nat, val) -> pure . VNum $ numVal val
  (_, val) -> pure val

numVal :: Val Z -> NumVal Z
numVal (VApp var B0) = nVar var
numVal (VNum val) = val
numVal val = error $ "Found a " ++ show val ++ " at Nat kind"

class Eval (f :: N -> Type) where
  type ValOf f :: Type
  eval :: Valz n             -- An environment for looking up VInxs
       -> f n                -- The thing we're evaluating
       -> Checking (ValOf f) -- An Inx-closed value

data Stan :: (N -> Type) -> (N -> Type) where
  (://) :: Scope f n -- A scope with the most local index missing
        -> Val Z     -- The thing to instantiate that index to
        -> Stan f n

instance Eval f => Eval (Stan f) where
  type ValOf (Stan f) = ValOf f
  eval ga ((de ::- x) :// v) = eval (ga <<+ de :<< v) x

instance Eval Val where
  type ValOf Val = Val Z
  eval ga (VLam (de ::- v)) = pure $ VLam ((ga <<+ de) ::- v)
  eval ga (VFun m cty) = case m of
    Braty -> VFun m <$> eval ga cty
    Kerny -> VFun m <$> eval ga cty
  eval ga (VApp f vz) = do
    f <- eval ga f
    vz <- traverse (eval ga) vz
    apply f vz
  eval ga (VNum n) = VNum <$> eval ga n
  eval ga (VCon c args) = VCon c <$> traverse (eval ga) args
  eval ga (VSum Kerny ts) = VSum Kerny <$> traverse (\(Some (Flip ro)) -> eval ga ro <&> \case
                                                        Left ro -> Some (Flip ro)
                                                        Right (ro, _) -> Some (Flip ro)) ts
  eval ga (VSum Braty ts) = VSum Braty <$> traverse (\(Some (Flip ro)) -> eval ga ro <&> \case
                                                        Left ro -> Some (Flip ro)
                                                        Right (ro, _) -> Some (Flip ro)) ts

apply :: Val Z -> Bwd (Val Z) -> Checking (Val Z)
apply f B0 = pure f
apply f (vz :< v) = apply f vz >>= \case
  VApp f vz -> pure $ VApp f (vz :< v)
  VLam sc -> eval S0 (sc :// v)
  v -> err $ InternalError $ "apply called on " ++ show v

instance Eval (Scope f) where
  type ValOf (Scope f) = Scope f Z
  eval ga (de ::- b) = pure (ga <<+ de ::- b)

-- We have to talk about `Ro'` (which has top and bottom the wrong way round) here
-- Generally, we should only consider the type alias: Ro
--instance MODEY m => Eval (Ro' m top) where
instance EvMode m => Eval (Ro' m top) where
  type ValOf (Ro' m top) = Either (Ro m Z top) (Ro m Z Z, Valz top)
  eval ga R0 = pure $ Right (R0, ga)
  eval ga (REx b sc) = eval ga sc <&> \sc -> Left (REx b sc)
  eval ga (RPr (x,s) r) = do
    s <- eval ga s
    eval ga r <&> \case
      Left r -> Left (RPr (x, s) r)
      Right (r, ga) -> Right (RPr (x, s) r, ga)

instance EvMode m => Eval (CTy m) where
  type ValOf (CTy m) = CTy m Z
  eval ga (ri :->> ro) = eval ga ri >>= \case
    Left ri -> pure (ri :->> ro)
    Right (ri, ga) -> eval ga ro <&> \case
      Left ro -> ri :->> ro
      Right (ro, _) -> ri :->> ro

instance Eval VVar where
  type ValOf VVar = Val Z
  eval ga (VInx i) = pure $ proj ga i
  eval _ (VLvl l s) = pure $ VApp (VLvl l s) B0
  eval _ (VPar x) = req (ELup x) >>= \case
    -- v is closed, because it came from the store, but not necessarily in
    -- normal form because it could contain more defined "Par"s.
    -- We can keep going because we don't put recursive definitions in the store.
    Just v -> eval S0 v
    Nothing -> pure $ VApp (VPar x) B0

instance Eval NumVal where
  type ValOf NumVal = NumVal Z
  eval l (NumValue up grow) = nPlus up <$> eval l grow

instance Eval Fun00 where
  type ValOf Fun00 = NumVal Z
  eval _ Constant0 = pure (nConstant 0)
  eval l (StrictMonoFun sm) = eval l sm

instance Eval StrictMono where
  type ValOf StrictMono = NumVal Z
  eval l (StrictMono pow mono) = n2PowTimes pow <$> eval l mono

instance Eval Monotone where
  type ValOf Monotone = NumVal Z
  eval l (Linear v) = numVal <$> eval l v
  eval l (Full sm) = nFull <$> eval l sm

{-
instance (Eval s, Eval t) => Eval (Either s t) where
  type ValOf (Either s t) = Either (ValOf s) (ValOf t)
  eval g l (Left s) = Left <$> eval g l s
  eval g l (Right t) = Right <$> eval g l t

instance Eval TypeKind where
  type ValOf TypeKind = TypeKind
  eval _ _ = pure
-}

kindEq :: TypeKind -> TypeKind -> Either ErrorMsg ()
kindEq Nat Nat = Right ()
kindEq (TypeFor m xs) (TypeFor m' ys) | m == m' = kindListEq xs ys
 where
  kindListEq :: [(PortName, TypeKind)] -> [(PortName, TypeKind)] -> Either ErrorMsg ()
  kindListEq [] [] = Right ()
  kindListEq ((_, x):xs) ((_, y):ys) = kindEq x y *> kindListEq xs ys
  kindListEq _ _ = Left $ TypeErr "Unequal kind lists"
kindEq k k' = Left . TypeErr $ "Unequal kinds " ++ show k ++ " and " ++ show k'

kindOf :: VVar Z -> Checking TypeKind
kindOf (VLvl _ k) = pure k
kindOf (VPar e) = req (TypeOf e) >>= \case
  EndType Braty (Left k) -> pure k
  EndType my ty -> typeErr $ "End " ++ show e ++ " isn't a kind, it's type is " ++ case my of
    Braty -> show ty
    Kerny -> show ty
kindOf (VInx n) = case n of {}

-- We should have made sure that the two values share the given kind
eq :: String -- String representation of the term for error reporting
   -> Int -- Next available de Bruijn level
   -> TypeKind -- The kind we're comparing at
   -> Val Z -- Expected
   -> Val Z -- Actual
   -> Checking ()
eq str i k exp act = eqTest str i k exp act >>= throwLeft

eqTest :: String -- String representation of the term for error reporting
       -> Int -- Next available de Bruijn level
       -> TypeKind -- The kind we're comparing at
       -> Val Z -- Expected
       -> Val Z -- Actual
       -> Checking (Either ErrorMsg ())
eqTest tm l k exp act = (k,,) <$> standardise k exp <*> standardise k act >>= \case
  (TypeFor m ((_, k):ks), f, g) -> do
    let x = varVal k (VLvl l k)
    f <- apply f (B0 :< x)
    g <- apply g (B0 :< x)
    eqTest tm (l + 1) (TypeFor m ks) f g
  -- Nothing else is higher kinded
  -- Invariant: Everything of kind Nat is a VNum
  (Nat, VNum n, VNum m) | n == m -> pure (Right ())
  (TypeFor m [], VApp v ss, VApp v' ss')
    | v == v' -> kindOf v >>= \case
        -- eqs should succeed if ks,ss,ss' are all []
        TypeFor m' ks | m == m' -> eqTests tm l (snd <$> ks) (ss <>> []) (ss' <>> [])
        k' -> pure . Left $ KindMismatch (show tm) (show k) (show k')
  (TypeFor m [], VCon c vs, VCon c' vs')
    | c == c' -> req (TLup (m, c)) >>= \case
        Just ks -> eqTests tm l (snd <$> ks) vs vs'
        Nothing -> pure . Left . TypeErr $ "Type constructor " ++ show c ++ " undefined " ++ " at kind " ++ show (TypeFor m [])
  (Star [], VFun m0 cty0, VFun m1 cty1) | Just Refl <- testEquality m0 m1 -> evModily m0 $ eqCTypeTest tm m0 l cty0 cty1
  (TypeFor _m [], VSum my0 ros0, VSum my1 ros1) -> case testEquality my0 my1 of
    Nothing -> pure (Left (InternalError "Mismatched modes in sums"))
    Just Refl -> if (length ros0 /= length ros1)
                 then pure (Left (TypeErr "Mismatched sum lengths"))
                 else do
      tests :: [Either ErrorMsg ()] <- zipWithM (\(Some (Flip ro0)) (Some (Flip ro1)) -> bimap id (const ()) <$> modily my0 (eqRowTest "Sum eq" my0 0 ro0 ro1)) ros0 ros1
      case sequence tests of
        Right _ -> pure (Right ())
        Left err -> pure (Left err)

  (_, s, t) -> pure . Left $ TypeMismatch tm (show s) (show t)

typeEq :: String -- String representation of the term for error reporting
   -> TypeKind -- The kind we're comparing at
   -> Val Z -- Expected
   -> Val Z -- Actual
   -> Checking ()
typeEq tm = eq tm 0

eqTests :: String -> Int -> [TypeKind] -> [Val Z] -> [Val Z] -> Checking (Either ErrorMsg ())
eqTests _ _ [] [] [] = pure (Right ())
eqTests tm l (k:ks) (u:us) (v:vs) = eqTest tm l k u v >>= \case
  Right () -> eqTests tm l ks us vs
  Left e -> pure $ Left e
eqTests _ _ _ us vs = pure . Left . TypeErr $ "Arity mismatch in type constructor arguments:\n  "
                   ++ show us ++ "\n  " ++ show vs

eqCTypeTest :: EvMode m
            => String
            -> Modey m
            -> Int -- Next de Bruijn level
            -> CTy m Z
            -> CTy m Z
            -> Checking (Either ErrorMsg ())
eqCTypeTest tm m de (ss0 :->> ts0) (ss1 :->> ts1) = do
  eqRowTest tm m de ss0 ss1 >>= \case
    Right (de, ga0, ga1) -> do
      -- The environments that we get back from the first eqRow call should make
      -- the top ends of the CTys zero after evaluation
      ts0 <- eval ga0 ts0
      ts1 <- eval ga1 ts1
      case (ts0, ts1) of
        (Left ts0, Left ts1) -> Right () <$ eqRowTest tm m de ts0 ts1
        (Right (ts0,_), Right (ts1,_)) -> Right () <$ eqRowTest tm m de ts0 ts1
        _ -> pure . Left . TypeErr $ "Mismatched function types! One binds and the other doesn't"
    Left e -> pure (Left e)

-- Type rows have i,j dangling de Bruijn indices, which we instantiate with
-- de Bruijn levels. As we go under binders in these rows, we add to the scope's
-- environments, which we return at the end for eqCType.
--
-- The top ends of both of the rows doesn't have to be equal. The Rows have a
-- stashed context which doesn't count towards equality
eqRowTest :: forall m i j
{-           . EvMode m
          => String
-}
           . String
          -> Modey m
          -> Int -- Next de Bruijn level
          -> Ro m Z i
          -> Ro m Z j
          -> Checking (Either ErrorMsg (Int, Valz i, Valz j))
eqRowTest tm my de ro0 ro1 = worker de (S0, ro0) (S0, ro1)
 where
  worker :: forall i0 i1 j0 j1. Int -> (Valz i0, Ro m i0 j0) -> (Valz i1, Ro m i1 j1) -> Checking (Either ErrorMsg (Int, Valz j0, Valz j1))
  worker de (env0, R0) (env1, R0) = pure $ Right (de, env0, env1)
  worker de (env0, RPr (_, ty0) ro0) (env1, RPr (_, ty1) ro1) = do
    ty0 <- eval env0 ty0
    ty1 <- eval env1 ty1
    r <- case my of
      -- We're comparing types of fields in a row, so the kind is always `Star []`
      -- ... if it were of kind Nat, it wouldn't be the type of a field
      Braty -> eqTest tm de (Star []) ty0 ty1
      Kerny -> eqTest tm de (Dollar []) ty0 ty1
    case r of
      Right () -> worker de (env0, ro0) (env1, ro1)
      Left e -> pure (Left e)
  -- ga0 and ga1 are too short by 1
  worker de (env0, REx (_, k0) (ga0 ::- r0)) (env1, REx (_, k1) (ga1 ::- r1))
    | k0 == k1 = let lvl = varVal k0 (VLvl de k0) in
        worker (de + 1) (env0 <<+ ga0 :<< lvl, r0) (env1 <<+ ga1 :<< lvl, r1)
  worker _ (_, _) (_, _) = modily my $
                           pure . Left . TypeErr $
                           "eqRow: failed at " ++ tm ++ " with rows " {-++ show ro0 ++ " and " ++ show ro1-}
