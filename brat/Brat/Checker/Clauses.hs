{-# LANGUAGE
AllowAmbiguousTypes,
UndecidableInstances
#-}

module Brat.Checker.Clauses (checkBody) where

import Brat.Checker
import Brat.Checker.Helpers hiding (track, trackM)
import Brat.Checker.Monad
import Brat.Checker.Types hiding (Store)
import Brat.Constructors
import Brat.Error
import Brat.Eval
import Brat.FC hiding (end)
import qualified Brat.FC as FC
import Brat.Graph (NodeType(..), MatchSequence(..), PrimTest(..), TestMatchData(..))
import Brat.Naming
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
import Data.Bifunctor
import Data.Foldable (traverse_)
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Type.Equality ((:~:)(..), testEquality)
import Brat.Syntax.Port (toEnd)

-- Top level function for type checking function definitions
-- Will make a top-level box for the function, then type check the definition
checkBody :: (CheckConstraints m UVerb, EvMode m, ?my :: Modey m)
          => String -- The function name
          -> FunBody Term UVerb
          -> CTy m Z -- Function type
          -> Checking Src
checkBody fnName body cty = case body of
  NoLhs tm -> do
    ((src, _), _) <- makeBox' fnName cty $ \(parent, _, overs, unders, _) -> check tm (overs, unders) $> parent
    pure src
  Clauses cs -> checkClauses ?my fnName (mkClause <$> (NE.zip (NE.fromList [0..]) cs)) cty
  Undefined -> err (InternalError "Checking undefined clause")
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

-- Return the tests that need to succeed for this clause to fire
-- (Tests are always defined on the overs of the outer box, rather than on
-- refined overs)
checkClause :: forall m. (CheckConstraints m UVerb, EvMode m) => Modey m
            -> String
            -> CTy m Z
            -> Clause
            -> Checking
               ( Name   -- TestMatch node (LHS)
               , Name   -- Function node (RHS)
               )
checkClause my fnName cty@(ins :->> _) clause = modily my $ do
  trackM $ "-------------\n\nCheckClause " ++ show clause
  let clauseName = fnName ++ "." ++ show (index clause)
  -- First, we check the patterns on the LHS. This requires some overs,
  -- so we make a box, however this box will never be turned into Hugr.
  (_, names) <- let ?my = my in makeBox (clauseName ++ "_setup") cty $ \(overs, unders) -> do
    -- Make a problem to solve based on the lhs and the overs
    problem <- argProblems (fst <$> overs) (unWC $ lhs clause) []
    (tests, sol) <- localFC (fcOf (lhs clause)) $ solve my problem
    -- The solution gives us the variables bound by the patterns.
    -- We turn them into a row
    Some (patEz :* Flip patRo) <- mkArgRo my S0 ((\(n, (src, ty)) -> (NamedPort (toEnd src) n, ty)) <$> sol)
    -- Also make a row for the refined outputs (shifted by the pattern environment)
    Some (_ :* Flip outRo) <- mkArgRo my patEz (first (fmap toEnd) <$> unders)


    -- Package up tests in a node. The output is a sum of the original inputs
    -- (if the tests failed) or the pattern variables (if the tests succeeded).
    -- We apply a thinning to weaken the type to the correct scope
    let insTop = roTopM my Zy ins
    let testOuts = RPr ("test_out", weaken insTop $ VSum my [Some (Flip ins), Some (Flip patRo)]) R0
    let match = TestMatch $ TestMatchData my $ MatchSequence overs tests (snd <$> sol)
    (testNode, _, _, _) <- let ?my = my in anext (clauseName ++ "_lhs") match (S0, Some (Zy :* S0)) ins testOuts

    -- Now actually make a box for the RHS and check it
    let rhsCty = patRo :->> outRo
    (_, rhsNode) <- makeBox' (clauseName ++ "_rhs") rhsCty $ \(node, _, rhsOvers, rhsUnders, _) -> do
      let abstractor = WC (fcOf (lhs clause)) $ foldr ((:||:) . APat . Bind . fst) AEmpty sol
      trackM (show abstractor)
      let fc = FC (start (fcOf (lhs clause))) (FC.end (fcOf (rhs clause)))
      let ?my = my in
        check @m (WC fc (abstractor :\: rhs clause)) (rhsOvers, rhsUnders)
      pure node
    pure (testNode, rhsNode)
  pure names

-- The ctype given should have the pattern variables from refining the lhs of the clause as its LHS
checkClauses :: forall m
              . (CheckConstraints m UVerb, EvMode m)
             => Modey m
             -> String
             -> NonEmpty Clause
             -> CTy m Z
             -> Checking Src
checkClauses my fnName clauses cty@(ins :->> outs) = do
  namess <- traverse (checkClause my fnName cty) clauses
  (_, _, [(over, _)], _) <- let ?my = my in anext fnName (FunClauses namess) (S0, Some (Zy :* S0))
                                            (R0 :: Ro m Z Z)
                                            ((RPr ("value", VFun modey (ins :->> outs)) R0) :: Ro m Z Z)
  pure over

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
type Problem = [({-Int,-} Src, Pattern)] -- let's not do fiddly positional arithmetic on the fly

typeOfSrc my src = typeOfEnd my (ExEnd (end src))

-- Solve is given a `Problem` (a mapping from wires to patterns) and uses this
-- to generate a mapping from each of the *pattern variables* in the patterns to
-- a specific wire. The wire isn't necessarily one of the inputs - we're adding
-- wiring to unpack constructors as well, and relating them to the wires given
-- in the problem via unification constraints.
--
-- This is insufficient though, we also need to work out:
--  1) What tests are performed in order to arrive at this branch
--  2) Exactly which inputs we're dropping before calling this branch
--  3) How to refine the original outputs
--
-- ... I guess 2 could be solved by comparing `Src`s in the solution to those we
-- had at the start...
solve :: forall m. Modey m
       -> Problem
       -> Checking (-- [(Int, Test)] -- too much too hugr too soon?
                    [(Src, PrimTest (BinderType m))]
                   ,[(String, (Src, BinderType m))] -- Remember the names given by programmers
                   )
solve _ [] = pure ([], [])
solve my ((src, DontCare):p) = do
  () <- case my of
    Kerny -> do
      ty <- typeOfSrc Kerny src
      if not (fromJust (copyable ty))
      then (typeErr $ "Ignoring linear variable of type " ++ show ty)
      else pure ()
    Braty -> pure ()
  solve my p
solve my ((src, Bind x):p) = do
  ty <- typeOfSrc my src
  (tests, sol) <- solve my p
  pure (tests, (x, (src, ty)):sol)
solve my ((src, Lit tm):p) = do
  ty <- typeOfSrc my src
  -- let's just check the literal is ok at this type, and maybe learn a number
  () <- case (my, ty) of
    (Braty, Left Nat)
      | Num n <- tm -> do
          unless (n >= 0) $ typeErr "Negative Nat kind"
          unifyNum (nConstant n) (nVar (VPar (ExEnd (end src))))
    (Braty, Right ty) -> do
      throwLeft (simpleCheck Braty ty tm)
    _ -> typeErr $ "Literal " ++ show tm ++ " isn't valid at this type"
  (tests, sol) <- solve my p
  pure ((src, PrimLitTest tm):tests, sol)
solve my ((src, PCon c abs):p) = do
  ty <- typeOfSrc my src
  case (my, ty) of
    -- TODO: When solving constructors, we need to provide actual wiring to get
    -- from the fully applied constructor to the bound pattern variables.
    -- E.g. for cons(x, xs), we need to actually take apart a Vec to get the x
    -- and xs to put in the environment
    (Kerny, ty) -> solveConstructor Kerny src (c, abs) ty p
    (Braty, Right ty) -> solveConstructor Braty src (c, abs) ty p
    (Braty, Left Nat) -> case c of
      -- Special case for 0, so that we can call `unifyNum` instead of pattern
      -- matching using what's returned from `natConstructors`
      PrefixName [] "zero" -> do
        unifyNum (nVar (VPar (ExEnd (end src)))) nZero
        p <- argProblems [] (normaliseAbstractor abs) p
        (tests, sol) <- solve my p
        pure ((src, PrimLitTest (Num 0)):tests, sol)
      _ -> case M.lookup c natConstructors of
        Just (Just _, relationToInner) -> do
          (node, [], kids@[(dangling, _)], _) <- next "unpacked_nat" Hypo (S0, Some (Zy :* S0))
            R0 -- we don't need to wire the src in; we just need the inner stuff
            (REx ("inner", Nat) (S0 ::- R0))
          unifyNum
           (nVar (VPar (ExEnd (end src))))
           (relationToInner (nVar (VPar (ExEnd (end dangling)))))
          p <- argProblems [dangling] (normaliseAbstractor abs) p
          (tests, sol) <- solve my p
          -- When we get @-patterns, we shouldn't drop this anymore
          pure ((src, PrimCtorTest c CNat node kids):tests, sol)
        _ -> typeErr $ "Couldn't find Nat constructor " ++ show c
    (Braty, Left k) -> typeErr $ "Pattern " ++ show c ++ " invalid for kind " ++ show k


typeOfEnd :: Modey m -> End -> Checking (BinderType m)
typeOfEnd my e = req (TypeOf e) >>= \case
  EndType my' ty
    | Just Refl <- testEquality my my' -> case my' of
        Braty -> case ty of
          Right ty -> Right <$> eval S0 ty
          _ -> pure ty
        Kerny -> eval S0 ty
    | otherwise -> err . InternalError $ "Expected end " ++ show e ++ " to be in a different mode"


solveConstructor :: EvMode m
                 => Modey m
                 -> Src
                 -> (UserName, Abstractor)
                 -> Val Z
                 -> Problem
                 -> Checking ([(Src, PrimTest (BinderType m))]
                             ,[(String, (Src, BinderType m))]
                             )
solveConstructor my src (c, abs) ty p = do
  (CArgs pats _ patRo argRo, (tycon, tyargs)) <- lookupConstructor my c ty
  (_, _, _, stuff) <- next "type_args" Hypo (S0, Some (Zy :* S0)) patRo R0
  (node, _, patArgWires, _) <- let ?my = my in anext "val_args" Hypo stuff R0 argRo
  trackM ("Constructor " ++ show c ++ "; type " ++ show ty)
  case (snd stuff) of
    Some (_ :* patEnds) -> do
      trackM (show pats)
      trackM (show patEnds)
      let (lhss, leftovers) = patVals pats (stkList patEnds)
      unless (null leftovers) $ error "There's a bug in the constructor table"
      tyArgKinds <- tlup (Brat, tycon)
      -- Constrain tyargs to match pats
      trackM $ unlines ["unifys",show lhss,show tyArgKinds, show tyargs]
      unifys lhss (snd <$> tyArgKinds) tyargs
      p <- argProblems (fst <$> patArgWires) (normaliseAbstractor abs) p
      (tests, sol) <- solve my p
      pure ((src, PrimCtorTest c tycon node patArgWires) : tests, sol)

unifys :: [Val Z] -> [TypeKind] -> [Val Z] -> Checking ()
unifys [] [] [] = pure ()
unifys (l:ls) (k:ks) (r:rs) = unify l k r *> unifys ls ks rs
unifys _ _ _ = error "jagged unifyArgs lists"

-- Unify two Braty types
unify :: Val Z -> TypeKind -> Val Z -> Checking ()
unify l k r = do
  -- Only complain normalised terms
  (l, r) <- (,) <$> eval S0 l <*> eval S0 r
  eqTest "unify" 0 k l r >>= \case
    Right () -> pure ()
    Left _ -> case (l, r, k) of
      (VCon c args, VCon c' args', Star [])
        | c == c' -> do
            ks <- tlup (Brat, c)
            unifys args (snd <$> ks) args'
      (VCon c args, VCon c' args', Dollar [])
        | c == c' -> do
            ks <- tlup (Kernel, c)
            unifys args (snd <$> ks) args'
      (VNum l, VNum r, Nat) -> unifyNum l r
      (VApp (VPar x) B0, v, _) -> instantiateMeta x v
      (v, VApp (VPar x) B0, _) -> instantiateMeta x v
      -- TODO: Handle function types
      -- TODO: Postpone this problem instead of giving up. Stick it an a list of
      --       equations that we hope are true and check them once we've processed
      --       the whole `Problem`.
      (l, r, _) -> err . UnificationError $ "Can't unify " ++ show l ++ " with " ++ show r

instantiateMeta :: End -> Val Z -> Checking ()
instantiateMeta e val = do
  throwLeft (doesntOccur e val)
  req (Define e val)


-- Be conservative, fail if in doubt. Not dangerous like being wrong while succeeding
-- We can have bogus failures here because we're not normalising under lambdas
-- N.B. the value argument is normalised.
doesntOccur :: End -> Val n -> Either ErrorMsg ()
doesntOccur e (VNum nv) = case getNumVar nv of
  Just e' -> collision e e'
  _ -> pure ()
 where
  getNumVar :: NumVal n -> Maybe End
  getNumVar (NumValue _ (StrictMonoFun (StrictMono _ mono))) = case mono of
    Linear v -> case v of
      VPar e -> Just e
      _ -> Nothing
    Full sm -> getNumVar (numValue sm)
  getNumVar _ = Nothing
doesntOccur e (VApp var args) = case var of
  VPar e' -> collision e e' *> traverse_ (doesntOccur e) args
  _ -> pure ()
doesntOccur e (VCon _ args) = traverse_ (doesntOccur e) args
doesntOccur e (VLam (stash ::- body)) = doesntOccurStash stash *> doesntOccur e body
 where
  doesntOccurStash :: Stack i (Val Z) j -> Either ErrorMsg ()
  doesntOccurStash S0 = pure ()
  doesntOccurStash (zx :<< x) = doesntOccur e x *> doesntOccurStash zx
doesntOccur e (VFun my (ins :->> outs)) = case my of
  Braty -> doesntOccurRo my e ins *> doesntOccurRo my e outs
  Kerny -> doesntOccurRo my e ins *> doesntOccurRo my e outs
doesntOccur e (VSum my rows) = traverse_ (\(Some (Flip ro)) -> doesntOccurRo my e ro) rows

collision :: End -> End -> Either ErrorMsg ()
collision e v | e == v = Left . UnificationError $
                         show e ++ " is cyclic"
              | otherwise = pure ()

-- Is this numvalue just a var plus a constant?
isNumVar :: NumVal n -> Maybe (Int, Maybe End) -- Upshift, variable
isNumVar (NumValue n (StrictMonoFun (StrictMono 0 (Linear (VPar e))))) = Just (n, Just e)
isNumVar (NumValue n Constant0) = Just (n, Nothing)
isNumVar _ = Nothing

doesntOccurRo :: Modey m -> End -> Ro m i j -> Either ErrorMsg ()
doesntOccurRo _ _ R0 = pure ()
doesntOccurRo my e (RPr (_, ty) ro) = doesntOccur e ty *> doesntOccurRo my e ro
doesntOccurRo Braty e (REx _ (_ ::- ro)) = doesntOccurRo Braty e ro

-- Can be clever, but not for now
-- N.B. We should already have checked equality on both values if we didn't know
-- for sure that at least one contained a variable.
unifyNum :: NumVal Z -> NumVal Z -> Checking ()
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
  _ -> err . UnificationError $ "Couldn't unify " ++ show l ++ " with " ++ show r

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

argProblems :: [Src] -> NormalisedAbstractor -> Problem -> Checking Problem
argProblems srcs (NA (APull ps abs)) p = pullPorts portName show ps (map (, ()) srcs) >>= \srcs -> argProblems (fst <$> srcs) (NA abs) p
argProblems (src:srcs) na p | Just (pat, na) <- unconsNA na = ((src, pat):) <$> argProblems srcs na p
argProblems [] (NA AEmpty) p = pure p
argProblems _ _ _ = err $ UnificationError "Pattern doesn't match expected length for constructor args"

lookupConstructor :: Modey m
                  -> UserName -- A value constructor
                  -> Val Z    -- A corresponding type to normalise
                  -- TODO: Something with this m
                  -> Checking (CtorArgs m -- The needed args to the value constructor
                              ,(UserName, [Val Z])  -- The type constructor we normalised and its args
                              )
lookupConstructor my c ty = eval S0 ty >>= \case
  (VCon tycon args) -> (,(tycon, args)) <$> case my of
    Braty -> clup c tycon
    Kerny -> track ("kclup " ++ show c ++ " " ++ show tycon) $ kclup c tycon
  ty -> typeErr $ "Couldn't normalise type " ++ show ty ++ " to a constructor"

{-
data Test
  = Zero0Succ1
  | Nil0Cons1
  | False0True1
  | None0Some1
  | Not0Exactly1 SimpleTerm
  | Odd0Even1
  | Not Test
 deriving Show

natTest :: UserName -> Test
natTest CSucc = Zero0Succ1
natTest CDoub = Odd0Even1
natTest CZero = Not (Zero0Succ1)
-}

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


data Pair (t :: N -> Type) (n :: N) where
  (:&) :: t n -> t n -> Pair t n

data PatResult m
 = Indiscriminate
 | Discriminate (Test, Bool)
 | forall n. Invalid TypeOrKind (Val n)

type PortTest = (Int, Test)
-}
