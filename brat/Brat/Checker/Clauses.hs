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

import Control.Monad (unless)
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor (first)
import Data.Either (isRight)
import Data.Foldable (traverse_)
import Data.Functor ((<&>), ($>))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Type.Equality ((:~:)(..))

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

solve :: Modey m
      -> Problem
      -> Unify m (Solution m)
solve Braty p = solveBrat p
solve Kerny p = solveKern p

solveBrat :: Problem -> Unify Brat (Solution Brat)
solveBrat [] = pure []
solveBrat ((_, DontCare):p) = solveBrat p
solveBrat ((e, Bind x):p) = do
  ty <- typeOfEnd Braty e
  let v = endVal' Braty ty e
  ((x, (v, ty)):) <$> solveBrat p
solveBrat ((e, Lit tm):p) = do
  ty <- typeOfEnd Braty e
  case ty of
    Left Nat | Num n <- tm -> do
                 unless (n >= 0) $ throwError "Negative Nat kind"
                 unifyNum (nConstant n) (nVar (VPar e))
                 solveBrat p
    Left k -> throwError $ "Kind " ++ show k ++ " can't be literal " ++ show tm
    Right ty -> liftEither (first show (simpleCheck Braty ty tm)) *> solveBrat p
solveBrat ((e, pat@(PCon c abs)):p) = do
  ty <- typeOfEnd Braty e
  -- Need to get rid of kinds
  case ty of
    Right ty -> solveConstructor (c, abs) ty p
    Left Nat -> case c of
      -- Special case for 0, so that we can call `unifyNum` instead of pattern
      -- matching using what's returned from `natConstructors`
      PrefixName [] "zero" -> do
        unifyNum (nVar (VPar e)) nZero
        p <- argProblems [] (normaliseAbstractor abs) p
        solveBrat p
      _ -> case M.lookup c natConstructors of
        Just (Just _, relationToInner) -> do
          innerEnd <- freshEnd (show c ++ "inner") (Left Nat)
          unifyNum (nVar (VPar e)) (relationToInner (nVar (VPar innerEnd)))
          p <- argProblems [("inner", innerEnd)] (normaliseAbstractor abs) p
          solveBrat p
        _ -> throwError $ "Couldn't find Nat constructor " ++ show c
    _ -> throwError $ "Pattern " ++ show pat ++ " invalid for type " ++ show ty

solveKern :: Problem -> Unify Kernel (Solution Kernel)
solveKern [] = pure []
solveKern ((_, DontCare):p) = solveKern p
solveKern ((e, Bind x):p) = do
  ty <- typeOfEnd Kerny e
  let v = endVal' Kerny ty e
  ((x, (v, ty)):) <$> solveKern p
solveKern ((e, Lit tm):p) = do
  ty <- typeOfEnd Kerny e
  liftEither (first show (simpleCheck Kerny ty tm)) *> solveKern p
-- TODO: Refactor so that this case can just be a call to `solveConstructor`
solveKern ((e, pat@(PCon c abs)):p) = do
  ty <- typeOfEnd Kerny e
  normalise ty >>= \case
    VCon tyCon tyArgs -> do
      CArgs pats nFree _tyArgRo argRo <- runChecker $ req (KCLup (FC (Pos 0 0) (Pos 0 0)) c tyCon)
      let na = normaliseAbstractor abs
      -- Fail when the types don't match up
      case valMatches tyArgs pats of
        Left err -> throwError (show err)
        Right (Some (ny :* valz)) -> do
          case natEqOrBust nFree ny of
            Left _ -> throwError "internal error in solveKern"
            Right Refl -> do
              (_, args) <- mkEndsForRo Kerny valz argRo
              p <- argProblems args na p
              solveKern p
    _ -> throwError $ "Pattern " ++ show pat ++ " invalid for type " ++ show ty

-- Solve a BRAT constructor.
solveConstructor :: (UserName, Abstractor) -> Val Z -> Problem -> Unify Brat (Solution Brat)
solveConstructor (c, abs) ty p = do
  (CArgs pats _ patRo argRo, (tycon, tyargs)) <- lookupConstructor Braty c ty
  (stk, patEnds) <- mkEndsForRo Braty S0 patRo
  (_, argEnds) <- mkEndsForRo Braty stk argRo
  trackM ("Constructor " ++ show c ++ "; type " ++ show ty)
  let (lhss, leftovers) = patVals pats (snd <$> patEnds)
  unless (null leftovers) $ error "There's a bug in the constructor table"
  tyargKinds <- lookupTypeConstructorArgs Brat tycon
  -- Constrain tyargs to match pats
  unifys lhss (snd <$> tyargKinds) tyargs
  p <- argProblems argEnds (normaliseAbstractor abs) p
  solve Braty p

unifys :: [Val Z] -> [TypeKind] -> [Val Z] -> Unify Brat ()
unifys [] [] [] = pure ()
unifys (l:ls) (k:ks) (r:rs) = unify l k r *> unifys ls ks rs
unifys _ _ _ = error "jagged unifyArgs lists"

-- Unify two Braty types
unify :: Val Z -> TypeKind -> Val Z -> Unify Brat ()
unify l k r = do
  (l, r) <- (,) <$> normalise l <*> normalise r
  b <- equal Braty k l r
  if b
  then pure ()
  else case (l, r, k) of
    (VCon c args, VCon c' args', Star [])
      | c == c' -> do
          ks <- lookupTypeConstructorArgs Brat c
          unifys args (snd <$> ks) args'
    (VCon c args, VCon c' args', Dollar [])
      | c == c' -> do
          ks <- lookupTypeConstructorArgs Kernel c
          unifys args (snd <$> ks) args'
    (VNum l, VNum r, Nat) -> unifyNum l r
    (VApp (VPar x) B0, v, _) -> instantiateMeta x v
    (v, VApp (VPar x) B0, _) -> instantiateMeta x v
    -- TODO: Handle function types
    -- TODO: Postpone this problem instead of giving up. Stick it an a list of
    --       equations that we hope are true and check them once we've processed
    --       the whole `Problem`.
    (l, r, _) -> throwError $ "Can't unify " ++ show l ++ " with " ++ show r

instantiateMeta :: End -> Val Z -> Unify m ()
instantiateMeta e val = do
  st <- get
  let ev = endVals st
  liftEither (doesntOccur ev e val)
  let ev' = M.insert e val ev
  put (st { endVals = ev' })


-- Be conservative, fail if in doubt. Not dangerous like being wrong while succeeding
-- We can have bogus failures here because we're not normalising under lambdas
doesntOccur :: M.Map End (Val Z) -> End -> Val n -> Either String ()
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
  VPar e' -> chaseDefn endVals e e' *> traverse_ (doesntOccur endVals e) args
  _ -> pure ()
doesntOccur endVals e (VCon _ args) = traverse_ (doesntOccur endVals e) args
doesntOccur endVals e (VLam (stash ::- body)) = doesntOccurStash stash *> doesntOccur endVals e body
 where
  doesntOccurStash :: Stack i (Val Z) j -> Either String ()
  doesntOccurStash S0 = pure ()
  doesntOccurStash (zx :<< x) = doesntOccur endVals e x *> doesntOccurStash zx
doesntOccur endVals e (VFun my (ins :->> outs)) = case my of
  Braty -> doesntOccurRo my endVals e ins *> doesntOccurRo my endVals e outs
  Kerny -> doesntOccurRo my endVals e ins *> doesntOccurRo my endVals e outs

chaseDefn :: M.Map End (Val Z) -- `endVals` from the Store
          -> End -> End -> Either String ()
chaseDefn endVals e v | e == v = throwError $ show e ++ " is cyclic"
                      | otherwise = case M.lookup v endVals of
                          Nothing -> pure ()
                          Just defn -> doesntOccur endVals e defn


-- Is this numvalue just a var plus a constant?
isNumVar :: NumVal n -> Maybe (Int, Maybe End) -- Upshift, variable
isNumVar (NumValue n (StrictMonoFun (StrictMono 0 (Linear (VPar e))))) = Just (n, Just e)
isNumVar (NumValue n Constant0) = Just (n, Nothing)
isNumVar _ = Nothing

doesntOccurRo :: Modey m -> M.Map End (Val Z) -> End -> Ro m i j -> Either String ()
doesntOccurRo _ _ _ R0 = pure ()
doesntOccurRo my endVals e (RPr (_, ty) ro) = doesntOccur endVals e ty *> doesntOccurRo my endVals e ro
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

getStore :: Unify m (Store m)
getStore = get

equal :: Modey m -> TypeKind -> Val Z -> Val Z -> Unify m Bool
equal _ k l r = do
  st <- getStore
  pure $ isRight (runExcept $ evalStateT (runChecker $ typeEq "" k l r) st)

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
mkEndsForRo :: Modey m -> Stack Z (Val Z) i -> Ro m i j -> Unify m (Stack Z (Val Z) j, [(PortName, End)])
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
lookupConstructor :: Modey m
                  -> UserName -- A value constructor
                  -> Val Z    -- A corresponding type to normalise
                  -- TODO: Something with this m
                  -> Unify Brat (CtorArgs m -- The needed args to the value constructor
                                ,(UserName, [Val Z])  -- The type constructor we normalised and its args
                                )
lookupConstructor my c ty = runChecker (eval S0 ty) >>= \case
  ty@(VCon cty args) -> case M.lookup c (constructorTable my) >>= M.lookup cty of
                         Just ctorArgs -> pure (ctorArgs, (cty, args))
                         Nothing -> throwError $ "Couldn't find constructor " ++ show c ++ " for type " ++ show ty
  ty -> throwError $ "Couldn't normalise type " ++ show ty ++ " to a constructor"
 where
  constructorTable :: Modey m -> ConstructorMap m
  constructorTable Braty = defaultConstructors
  constructorTable Kerny = kernelConstructors

lookupTypeConstructorArgs :: Mode -> UserName -> Unify m' [(String, TypeKind)]
lookupTypeConstructorArgs m tycon = case M.lookup (m, tycon) defaultTypeConstructors of
  Just ks -> pure ks
  _ -> throwError $ "Invalid type constructor " ++ show tycon

-- Run a `Checking` computation, but substituting our own store for `ELup`, and
-- complain if it requests much else.
runChecker :: Free CheckingSig v -> Unify m v
runChecker (Ret v) = pure v
runChecker (Req (ELup e) k) = get >>= \st -> runChecker $ k (M.lookup e (endVals st))
-- TODO: This will need to change to using the proper Checking Monad before we
-- can handle user defined value constructors
runChecker (Req (KCLup _ tmCon tyCon) k) = case M.lookup tmCon kernelConstructors of
  Nothing -> throwError ("Invalid constructor " ++ show tmCon)
  Just tbl -> case M.lookup tyCon tbl of
    Nothing -> throwError (show tmCon ++ " isn't a valid constructor for " ++ show tyCon)
    Just answer -> runChecker $ k answer

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
 | forall n. Invalid TypeOrKind (Val n)

type PortTest = (Int, Test)
-}
