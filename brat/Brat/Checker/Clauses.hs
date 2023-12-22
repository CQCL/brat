{-# LANGUAGE
AllowAmbiguousTypes,
FlexibleContexts,
MultiParamTypeClasses,
ScopedTypeVariables,
TypeApplications,
UndecidableInstances
#-}

module Brat.Checker.Clauses where

import Brat.Checker
import Brat.Checker.Helpers
import Brat.Checker.Monad (err, throwLeft, localEnv)
import Brat.Checker.Types hiding (Store)
import Brat.Constructors
import Brat.Error
import Brat.Eval
import Brat.FC hiding (end)
import Brat.Naming
import Brat.Checker.Quantity (Quantity(One))
import Brat.Syntax.Abstractor
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Control.Monad.Freer
import Hasochism

import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor (first)
import Data.Either (isRight)
import Data.Foldable (traverse_)
import Data.Functor ((<&>), ($>))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Kind (Type)

import Debug.Trace

track = const (const id) trace

trackM :: Monad m => String -> m ()
trackM = const (pure ())

-- Top level function for type checking function definitions
checkBody :: (CheckConstraints m UVerb, EvMode m, ?my :: Modey m)
          => String -- The function name
          -> FunBody Term UVerb
          -> CTy m Z -- Function type
          -> Checking Src
checkBody fnName body cty = do
  ((src, _), ())<- makeBox fnName cty $ \(overs, unders) -> case body of
    -- Ignore outermost overs and unders - but we'll need them later
    Clauses cs -> checkClauses fnName (mkClause <$> (NE.zip (NE.fromList [0..]) cs)) cty
    NoLhs tm -> check tm (overs, unders) $> ()
    Undefined -> err (InternalError "Checking undefined clause")
  pure src
 where
  mkClause (i, (abs, tm)) = Clause i (normaliseAbstractor <$> abs) tm

-- Clauses from either function definitions or case statements (TODO), as we get
-- from the elaborator
data Clause = Clause
  { index :: Int  -- Which clause is this (in the order they're defined in source)
  , lhs :: WC NormalisedAbstractor
  , rhs :: WC (Term Chk Noun)
  }
 deriving Show

checkClauses :: (?my :: Modey m, CheckConstraints m UVerb, EvMode m)
             => String
             -> NonEmpty Clause
             -> CTy m Z
             -> Checking ()
checkClauses fnName clauses cty = flip traverse_ clauses $ \clause -> do
  let clauseName = fnName ++ "." ++ show (index clause)
  makeBox clauseName cty $ \(overs, unders) -> do
    ns <- req (FreshSupply clauseName)
    let st = Store M.empty overs ns
    -- Make a problem to solve based on the lhs and the overs
    let worker = argProblems ((\(NamedPort e name, _) -> (name, ExEnd e)) <$> overs) (unWC $ lhs clause) []
    (sol, st) <- throwLeft $ first UnificationError $ runExcept $ runStateT (solve ?my =<< worker) st
    -- Add our new ends to the Checking environment
    trackM (show st)
    case ?my of
      Braty -> traverse_ (req . uncurry Declare)
        [ (ExEnd (end src), k)
        | (src, Left k) <- ctx st
        -- Make sure we don't redeclare the things that we seeded ctx with
        , not (end src `elem` (end . fst <$> overs))
        ]
      _ -> pure ()
    -- Define them all according to endVals
    -- They might be in scope for our solution so we need them!
    traverse (req . uncurry Define) (M.toList $ endVals st)
    -- instantiate variables in `rhs` of clauses with the ends in our solution (localVEnv)
    env <- envFromSolution ?my sol
    -- type check the rhs
    (((), ()), ((), [])) <- localEnv env $ check (rhs clause) ((), unders)
    pure ()

-- Make fresh Ends on the graph and define them to our endVals answers
-- Make an `Env` from this that we can use to contextualise pattern vars in an RHS
envFromSolution :: Modey m -> Solution m -> Checking (Env (EnvData m))
envFromSolution my sol = M.fromList <$> traverse (envElem my) sol
 where
  envElem :: Modey m -> (String, (BinderVal m, BinderType m)) -> Checking (UserName, EnvData m)
  envElem my (name, (val, ty)) = do
    freshName <- req (Fresh (name ++ "_end"))
    let outport = Ex freshName 0
    let end = ExEnd outport
    let src = NamedPort outport name
    case (my, ty) of
      (Braty, Left k) -> req (Declare end k) *> req (Define end val) $> (plain name, [(src, ty)])
      (Braty, _) -> pure (plain name, [(src, ty)])
      (Kerny, _) -> pure (plain name, (One, (src, ty)))


-- Refine clauses from function definitions (and potentially future case statements)
-- by processing each one in sequence. This will involve repeating tests for various
-- branches, the removal of which is a future optimisation.
--
-- We have `Clause`s which are produced by the elaborator, and we work out how
-- to turn each one into a series of tests to perform on the context (read: `Overs`)

-- Success looks like having a mapping from the variables in the source code (Abstractor)
-- to concrete values: the statically known values and types of the program variables.
--
-- N.B. we make no assumptions about the values and types being normalised wrt `endVals`
type Solution m = [(String, (BinderVal m, BinderType m))]

type Problem = [(End, Pattern)]

-- All of the things in scope
type Context m = [(Src, BinderType m)]

data Store m = Store
  { endVals :: M.Map End (Val Z)  -- Values for *some* of the things in the context
  , ctx :: Context m
  , ns :: Namespace
  }

instance Show (BinderType m) => Show (Store m) where
  show Store { .. } = unlines $ concat [[show ns], ("Context":(show <$> ctx)), ("endVals":(show <$> M.toList endVals))]

freshEnd :: String -> BinderType m -> Unify m End
freshEnd s ty = do
  st <- get
  let (freshName, namespace) = fresh s (ns st)
  let freshOutPort = Ex freshName 0
  let context = (NamedPort freshOutPort "", ty) : ctx st
  put (st { ns = namespace, ctx = context })
  pure (ExEnd freshOutPort)

type Unify m = StateT (Store m) (Except String)

-- Equations should only be between things of the same kind by the point we reach them in `unify`
-- ... in general, but since our kinds aren't dependent all equations are homogeneous.
data Equation = (Val Z, TypeKind) :=: Val Z
 deriving Show

solve :: Show (BinderType m)
      => Modey m
      -> Problem
      -> Unify m (Solution m)
solve _ [] = pure []
solve my ((_, DontCare):p) = solve my p
solve my ((e, Bind x):p) = do
  ty <- typeOfEnd my e
  let v = endVal' my ty e
  ((x, (v, ty)):) <$> solve my p
solve my ((e, Lit tm):p) = do
  case my of
    Braty -> do
      ty <- typeOfEnd my e
      case ty of
        Left Nat | Num n <- tm -> do
          unless (n >= 0) $ throwError "Negative Nat kind"
          unifyNum (nConstant n) (nVar (VPar e))
          solve my p
        Left k -> throwError $ "Kind " ++ show k ++ " can't be literal " ++ show tm
        Right ty -> liftEither (first show (simpleCheck my ty tm)) *> solve my p
    Kerny -> do
      ty <- typeOfEnd my e
      liftEither (first show (simpleCheck my ty tm)) *> solve my p
solve my ((e, pat@(PCon c abs)):p) = do
  ty <- typeOfEnd my e
  -- Need to get rid of kinds and ensure we're in my = Braty
  case (my, ty) of
    (Braty, Right ty) -> solveConstructor (c, abs) ty p
    (Braty, Left Nat) -> case c of
      PrefixName [] "zero" -> do
        unifyNum (nVar (VPar e)) nZero
        p <- argProblems [] (normaliseAbstractor abs) p
        solve my p
      _ -> case M.lookup c natConstructors of
        Just (Just _, relationToInner) -> do
          innerEnd <- freshEnd (show c ++ "inner") (Left Nat)
          unifyNum (nVar (VPar e)) (relationToInner (nVar (VPar innerEnd)))
          p <- argProblems [("inner", innerEnd)] (normaliseAbstractor abs) p
          solve my p
        _ -> throwError $ "Couldn't find Nat constructor " ++ show c
    (Kerny, ty) -> normalise ty >>= \case
      -- And constrain to 0 if the length pattern is "nil"
      ty@(VOf sty len) -> do
        case (c, normaliseAbstractor abs) of
          (PrefixName [] "nil", na) -> do
            liftEither $ first show (numMatch B0 len NP0)
            p <- argProblems [] na p
            solve my p
          (PrefixName [] "cons", na) -> do
            liftEither (first show (numMatch B0 len (NP1Plus NPVar))) >>= \case
              B0 :< VNum lenPred -> do
                headEnd <- freshEnd "VOf head" sty
                let tailTy = VOf sty lenPred
                tailEnd <- freshEnd "VOf tail" tailTy
                -- These port names should be canonical, but we're making them up here
                p <- argProblems [("head", headEnd), ("tail", tailEnd)] na p
                solve my p
              _ -> throwError "Length for Vec wasn't a successor"
          (name, _) -> throwError $ "Pattern " ++ show name ++ " invalid for type " ++ show ty
      VBit
        | PrefixName [] x <- c, x `elem` ["true","false"] -> do
            p <- argProblems [] (normaliseAbstractor abs) p
            solve my p
      _ -> throwError $ "Pattern " ++ show pat ++ " invalid for type " ++ show ty
    _ -> throwError $ "Pattern " ++ show pat ++ " invalid for type " ++ show ty

solveConstructor :: (UserName, Abstractor) -> Val Z -> Problem -> Unify Brat (Solution Brat)
solveConstructor (c, abs) ty p = do
  (CArgs pats _ patRo argRo, (tycon, tyargs)) <- lookupConstructor c ty
  (stk, patEnds) <- mkEndsForRo Braty S0 patRo
  (_, argEnds) <- mkEndsForRo Braty stk argRo
  trackM ("Constructor " ++ show c ++ "; type " ++ show ty)
  let (lhss, leftovers) = patVals pats (snd <$> patEnds)
  unless (null leftovers) $ error "There's a bug in the constructor table"
  tyargKinds <- lookupTypeConstructorArgs tycon
  -- Constrain tyargs to match pats
  unifys Braty lhss (KfB . snd <$> tyargKinds) tyargs
  p <- argProblems argEnds (normaliseAbstractor abs) p
  solve Braty p

unifys :: Show (ValueType m Z) => Modey m -> [ValueType m Z] -> [KindFor m] -> [ValueType m Z] -> Unify m ()
unifys _ [] [] [] = pure ()
unifys my (l:ls) (k:ks) (r:rs) = unify my l k r *> unifys my ls ks rs
unifys _ _ _ _ = error "jagged unifyArgs lists"

unify :: Show (ValueType m Z) => Modey m -> ValueType m Z -> KindFor m -> ValueType m Z -> Unify m ()
unify my l k r = do
  (l, r) <- case my of
    Braty -> (,) <$> normalise l <*> normalise r
    Kerny -> (,) <$> normalise l <*> normalise r
  b <- equal my k l r
  if b
  then pure ()
  else case (my, l, r, k) of
    (Braty, VCon c args, VCon c' args', KfB (Star []))
      | c == c' -> do
          ks <- lookupTypeConstructorArgs c
          unifys Braty args (KfB . snd <$> ks) args'
    (Braty, VNum l, VNum r, KfB Nat) -> unifyNum l r
    (Braty, VApp (VPar x) B0, v, _) -> instantiateMeta x v
    (Braty, v, VApp (VPar x) B0, _) -> instantiateMeta x v
    (Kerny, VOf ty n, VOf ty' n', _) -> do
      unifyNum n n'
      unify Kerny ty KfK ty'
    (_, l, r, _) -> throwError $ "Can't unify " ++ show l ++ " with " ++ show r

instantiateMeta :: End -> Val Z -> Unify m ()
instantiateMeta e val = do
  st <- get
  let ev = endVals st
  liftEither (doesntOccur @Brat ev e val)
  let ev' = M.insert e val ev
  put (st { endVals = ev' })


class Occurs (m :: Mode) where
  doesntOccur :: M.Map End (Val Z) -> End -> ValueType m n -> Either String ()

-- Be conservative, fail if in doubt. Not dangerous like being wrong while succeeding
-- We can have bogus failures here because we're not normalising under lambdas
instance Occurs Brat where
  doesntOccur endVals e (VNum nv) = case getNumVar nv of
    Just e' -> chaseDefn endVals e e'
    _ -> pure ()
   where
    getNumVar :: NumVal n -> Maybe End
    getNumVar (NumValue _ (StrictMonoFun (StrictMono _ mono))) = case mono of
      Linear v -> case v of
        VPar e -> Just e
        _ -> Nothing
      Full sm -> getNumVar (numValue sm)
    getNumVar _ = Nothing
  doesntOccur endVals e (VApp var args) = case var of
    VPar e' -> chaseDefn endVals e e' *> traverse_ (doesntOccur @Brat endVals e) args
    _ -> pure ()
  doesntOccur endVals e (VCon _ args) = traverse_ (doesntOccur @Brat endVals e) args
  doesntOccur endVals e (VLam (stash ::- body)) = doesntOccurStash stash *> doesntOccur @Brat endVals e body
   where
    doesntOccurStash :: Stack i (Val Z) j -> Either String ()
    doesntOccurStash S0 = pure ()
    doesntOccurStash (zx :<< x) = doesntOccur @Brat endVals e x *> doesntOccurStash zx
  doesntOccur endVals e (VFun my (ins :->> outs)) = case my of
    Braty -> doesntOccurRo my endVals e ins *> doesntOccurRo my endVals e outs
    Kerny -> doesntOccurRo my endVals e ins *> doesntOccurRo my endVals e outs

instance Occurs Kernel where
  doesntOccur endVals e (VOf ty n) = doesntOccur @Kernel endVals e ty *> doesntOccur @Brat endVals e (VNum n)
  doesntOccur endVals e (VRho ro) = doesntOccurRo Kerny endVals e ro
  doesntOccur _ _ VBit = pure ()
  doesntOccur _ _ VQ = pure ()

chaseDefn :: M.Map End (Val Z) -- `endVals` from the Store
          -> End -> End -> Either String ()
chaseDefn endVals e v | e == v = throwError $ show e ++ " is cyclic"
                      | otherwise = case M.lookup v endVals of
                          Nothing -> pure ()
                          Just defn -> doesntOccur @Brat endVals e defn


-- Is this numvalue just a var plus a constant?
isNumVar :: NumVal n -> Maybe (Int, Maybe End) -- Upshift, variable
isNumVar (NumValue n (StrictMonoFun (StrictMono 0 (Linear (VPar e))))) = Just (n, Just e)
isNumVar (NumValue n Constant0) = Just (n, Nothing)
isNumVar _ = Nothing

doesntOccurRo :: Modey m -> M.Map End (Val Z) -> End -> Ro m i j -> Either String ()
doesntOccurRo _ _ _ R0 = pure ()
doesntOccurRo my@Braty endVals e (RPr (_, ty) ro) = doesntOccur @Brat endVals e ty *> doesntOccurRo my endVals e ro
doesntOccurRo my@Kerny endVals e (RPr (_, ty) ro) = doesntOccur @Kernel endVals e ty *> doesntOccurRo my endVals e ro
doesntOccurRo Braty endVals e (REx _ (_ ::- ro)) = doesntOccurRo Braty endVals e ro

-- Can be clever, but not for now
-- N.B. We should already have checked equality on both values if we didn't know
-- for sure that at least one contained a variable.
unifyNum :: NumVal Z -> NumVal Z -> Unify m ()
unifyNum l r = case (isNumVar l, isNumVar r) of
  (Just (0, Just x), _) -> instantiateMeta x (VNum r)
  (_, Just (0, Just y)) -> instantiateMeta y (VNum l)
  -- This is where interesting things will happen
  (Just (n, Nothing), Just (m, Just y))
    | n >= m -> instantiateMeta y $ VNum $ nConstant (n - m)
  (Just (n, Just x), Just (m, Nothing))
    | n <= m -> instantiateMeta x $ VNum $ nConstant (m - n)
  (Just (n, Just x), Just (m, Just y))
    | n <= m -> instantiateMeta x (VNum $ nPlus (m - n) (nVar (VPar y)))
    | otherwise -> instantiateMeta y (VNum $ nPlus (n - m) (nVar (VPar x)))
  _ -> throwError $ "Couldn't unify " ++ show l ++ " with " ++ show r

data KindFor :: Mode -> Type where
  KfB :: TypeKind -> KindFor Brat
  KfK :: KindFor Kernel

getStore :: Unify m (Store m)
getStore = get

equal :: Modey m -> KindFor m -> ValueType m Z -> ValueType m Z -> Unify m Bool
equal Braty (KfB k) l r = do
  st <- getStore
  pure $ isRight (runExcept $ evalStateT (runChecker $ typeEq "" k l r) st)
equal Kerny KfK l r = do
  st <- getStore
  pure $ isRight (runExcept $ evalStateT (runChecker $ stypeEq "" l r) st)

patVal :: ValPat -> [End] -> (Val Z, [End])
-- Nat variables will only be found in a `NumPat`, not a `ValPat`
patVal VPVar (e:es) = (VApp (VPar e) B0, es)
patVal (VPCon c args) es = case patVals args es of (args, es) -> (VCon c args, es)
patVal (VPNum np) es = case numPatVal np es of (n, es) -> (VNum n, es)
patVal pat [] = error $ "Constructor table has an error - no ends for " ++ show pat

patVals :: [ValPat] -> [End] -> ([Val Z], [End])
patVals (vp:vps) ends = case patVal vp ends of
  (v, ends) -> case patVals vps ends of
    (vs, ends) -> (v:vs, ends)
patVals [] ends = ([], ends)

numPatVal :: NumPat -> [End] -> (NumVal Z, [End])
numPatVal NPVar (e:es) = (nVar (VPar e), es)
numPatVal NP0 es = (nConstant 0, es)
numPatVal (NP1Plus np) es = case numPatVal np es of (nv, es) -> (nPlus 1 nv, es)
numPatVal (NP2Times np) es = case numPatVal np es of (nv, es) -> (n2PowTimes 1 nv, es)
numPatVal _ [] = error "Constructor table has an error (numPat)"

argProblems :: [(PortName, End)] -> NormalisedAbstractor -> Problem -> Unify m Problem
argProblems ends (NA (APull ps abs)) p
  = runChecker (pullPorts id show ps ends) >>= \ends -> argProblems ends (NA abs) p
argProblems ((_, e):ends) na p | Just (pat, na) <- unconsNA na = ((e, pat):) <$> argProblems ends na p
argProblems [] (NA AEmpty) p = pure p
argProblems _ _ _ = throwError "Pattern doesn't match expected length for constructor args"

-- Make new ends and put them in the context
mkEndsForRo :: DeBruijn (ValueType m) => Modey m -> Stack Z (Val Z) i -> Ro m i j -> Unify m (Stack Z (Val Z) j, [(PortName, End)])
mkEndsForRo _ stk R0 = pure (stk, [])
mkEndsForRo my stk (RPr (p, ty) ro) = do
  ty <- case my of
    Braty -> runChecker $ eval stk ty
    Kerny -> runChecker $ eval stk ty
  end <- freshEnd p (valueToBinder my ty)

  (stk, pes) <- mkEndsForRo my stk ro
  pure (stk, (p, end):pes)
-- TODO:
mkEndsForRo Braty stk (REx (p, k) (stash ::- ro)) = do
  end <- freshEnd p (Left k)
  (stk, ends) <- mkEndsForRo Braty (stk <<+ stash :<< (endVal k end)) ro
  pure (stk, (p,end):ends)

normalise :: Eval t => t Z -> Unify m (ValOf t)
normalise = runChecker . eval S0

-- HACK: For now, use the hard coded constructor map in `Constructors.hs`, rather
-- than the updatable one in the `Checking` monad
lookupConstructor :: UserName -- A value constructor
                  -> Val Z    -- A corresponding type to normalise
                  -> Unify Brat (CtorArgs -- The needed args to the value constructor
                                ,(UserName, [Val Z])  -- The type constructor we normalised and its args
                                )
lookupConstructor c ty = runChecker (eval S0 ty) >>= \case
  ty@(VCon cty args) -> case M.lookup c defaultConstructors >>= M.lookup cty of
                         Just ctorArgs -> pure (ctorArgs, (cty, args))
                         Nothing -> throwError $ "Couldn't find constructor " ++ show c ++ " for type " ++ show ty
  ty -> throwError $ "Couldn't normalise type " ++ show ty ++ " to a constructor"

lookupTypeConstructorArgs :: UserName -> Unify Brat [(String, TypeKind)]
lookupTypeConstructorArgs tycon = case M.lookup tycon defaultTypeConstructors of
  Just (Star ks) -> pure ks
  _ -> throwError $ "Invalid type constructor " ++ show tycon

-- Run a `Checking` computation, but substituting our own store for `ELup`, and
-- complain if it requests much else.
runChecker :: Free CheckingSig v -> Unify m v
runChecker (Ret v) = pure v
runChecker (Req (ELup e) k) = get >>= \st -> runChecker $ k (M.lookup e (endVals st))
runChecker (Req (Throw err) _) = throwError (showError err)
-- Provide a dummy FC because it'll probably be asked for before an error is thrown
runChecker (Req AskFC k) = runChecker $ k (FC (Pos 0 0) (Pos 0 0))
runChecker (Req _ _) = error "eval does more than we thought"

typeOfEnd :: Modey m -> End -> Unify m (BinderType m)
typeOfEnd _ e = do
  ctx <- gets ctx
  case lookup e (first (ExEnd . end) <$> ctx) of
    Nothing -> error "Type missing from context!!"
    Just ty -> pure ty

valOfEnd :: End -> Unify Brat (Val Z)
valOfEnd e = do
  valMap <- gets endVals
  case M.lookup e valMap of
    Nothing -> typeOfEnd Braty e <&> \ty -> endVal' Braty ty e
    -- We can't directly create a variable as a kernel type
    Just v -> pure v










{-
data TestTree
  = Succeed -- An indiscriminate pattern
  | Fail -- This clause does not apply for the refinement
  | Test (Src, TestType) -- A wire which we need to run a test on
    Subst -- A way to relate the original context to the refined one
    TestTree {- false -} TestTree {- true -}
 deriving Show

-- Clauses from either function definitions or case statements (TODO), as we get
-- from the elaborator
data Clause m = Clause
  { index :: Int  -- Which clause is this (in the order they're defined in source)
  , lhs :: WC NormalisedAbstractor
  , rhs :: WC (Term Chk Noun)
  }
 deriving Show


data RefinedBranch m i j = RBranch
    -- A sequence of tests to perform to determine whether this branch should fire
  { tests :: [Maybe (Test, Bool)]
  , lhs :: WC NormalisedAbstractor
  , sub :: Subst
  , sig :: CTy m i j
  }

data Test
  = Zero0Succ1
  | Nil0Cons1
  | False0True1
  | None0Some1
  | Not0Exactly1 SimpleTerm
  | Odd0Even1
 deriving Show

data Pair (t :: N -> Type) (n :: N) where
  (:&) :: t n -> t n -> Pair t n

data PatResult m
 = Indiscriminate
 | Discriminate (Test, Bool)
 | forall n. Invalid TypeOrKind (ValueType m n)

type PortTest = (Int, Test)
-}
