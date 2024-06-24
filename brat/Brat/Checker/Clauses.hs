{-# LANGUAGE
AllowAmbiguousTypes,
UndecidableInstances
#-}

module Brat.Checker.Clauses (checkBody) where

import Brat.Checker
import Brat.Checker.Helpers
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
    ((src, _), _) <- makeBox fnName cty $ \(overs, unders) -> check tm (overs, unders)
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
               ( TestMatchData m -- TestMatch data (LHS)
               , Name   -- Function node (RHS)
               )
checkClause my fnName cty clause = modily my $ do
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


    let match = TestMatchData my $ MatchSequence overs tests (snd <$> sol)

    -- Now actually make a box for the RHS and check it
    let rhsCty = patRo :->> outRo
    ((boxPort, _ty), _) <- makeBox (clauseName ++ "_rhs") rhsCty $ \(rhsOvers, rhsUnders) -> do
      let abstractor = WC (fcOf (lhs clause)) $ foldr ((:||:) . APat . Bind . fst) AEmpty sol
      trackM (show abstractor)
      let fc = FC (start (fcOf (lhs clause))) (FC.end (fcOf (rhs clause)))
      let ?my = my in
        check @m (WC fc (Lambda (abstractor, rhs clause) [])) (rhsOvers, rhsUnders)
    let NamedPort {end=Ex rhsNode _} = boxPort
    pure (match, rhsNode)
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

doesntOccurRo :: Modey m -> End -> Ro m i j -> Either ErrorMsg ()
doesntOccurRo _ _ R0 = pure ()
doesntOccurRo my e (RPr (_, ty) ro) = doesntOccur e ty *> doesntOccurRo my e ro
doesntOccurRo Braty e (REx _ (_ ::- ro)) = doesntOccurRo Braty e ro

unifyNum :: NumVal Z -> NumVal Z -> Checking ()
unifyNum (NumValue lup lgro) (NumValue rup rgro)
  | lup <= rup = lhsFun00 lgro (NumValue (rup - lup) rgro)
  | otherwise  = lhsFun00 rgro (NumValue (lup - rup) lgro)
 where
  lhsFun00 :: Fun00 Z -> NumVal Z -> Checking ()
  lhsFun00 Constant0 num = demand0 num
  lhsFun00 (StrictMonoFun sm) num = lhsStrictMono sm num

  lhsStrictMono :: StrictMono Z -> NumVal Z -> Checking ()
  lhsStrictMono (StrictMono 0 mono) num = lhsMono mono num
  lhsStrictMono (StrictMono n mono) num = do
    num <- demandEven num
    lhsStrictMono (StrictMono (n - 1) mono) num

  lhsMono :: Monotone Z -> NumVal Z -> Checking ()
  lhsMono (Linear v) num = case v of
    VPar e -> instantiateMeta e (VNum num)
    _ -> case num of -- our only hope is to instantiate the RHS
      NumValue 0 (StrictMonoFun (StrictMono 0 (Linear (VPar (ExEnd e))))) -> instantiateMeta (toEnd e) (VNum (nVar v))
      _ -> err . UnificationError $ "Couldn't instantiate variable " ++ show v
  lhsMono (Full sm) (NumValue 0 (StrictMonoFun (StrictMono 0 (Full sm'))))
    = lhsStrictMono sm (NumValue 0 (StrictMonoFun sm'))
  lhsMono m@(Full _) (NumValue 0 gro) = lhsFun00 gro (NumValue 0 (StrictMonoFun (StrictMono 0 m)))
  lhsMono (Full sm) (NumValue up gro) = do
    smPred <- demandSucc sm
    unifyNum (n2PowTimes 1 (nFull smPred)) (NumValue (up - 1) gro)

  demand0 :: NumVal Z -> Checking ()
  demand0 (NumValue 0 Constant0) = pure ()
  demand0 n@(NumValue 0 (StrictMonoFun (StrictMono _ mono))) = case mono of
    Linear (VPar e) -> instantiateMeta e (VNum (nConstant 0))
    Full sm -> demand0 (NumValue 0 (StrictMonoFun sm))
    _ -> err . UnificationError $ "Couldn't force " ++ show n ++ " to be 0"
  demand0 n = err . UnificationError $ "Couldn't force " ++ show n ++ " to be 0"

  -- Complain if a number isn't a successor, else return its predecessor
  demandSucc :: StrictMono Z -> Checking (NumVal Z)
  --   2^k * x
  -- = 2^k * (y + 1)
  -- = 2^k + 2^k * y
  demandSucc (StrictMono k (Linear (VPar (ExEnd out)))) = do
    y <- mkPred out
    pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes k y
  --   2^k * full(n + 1)
  -- = 2^k * (1 + 2 * full(n))
  -- = 2^k + 2^(k + 1) * full(n)
  demandSucc (StrictMono k (Full nPlus1)) = do
    n <- demandSucc nPlus1
    pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes (k + 1) $ nFull n
  demandSucc n = err . UnificationError $ "Couldn't force " ++ show n ++ " to be a successor"

  -- Complain if a number isn't even, otherwise return half
  demandEven :: NumVal Z -> Checking (NumVal Z)
  demandEven n@(NumValue up gro) = case up `divMod` 2 of
    (up, 0) -> NumValue up <$> evenGro gro
    (up, 1) -> nPlus (up + 1) <$> oddGro gro
   where
    evenGro :: Fun00 Z -> Checking (Fun00 Z)
    evenGro Constant0 = pure Constant0
    evenGro (StrictMonoFun (StrictMono 0 mono)) = case mono of
      Linear (VPar (ExEnd out)) -> do
        half <- mkHalf out
        pure (StrictMonoFun (StrictMono 0 (Linear (VPar (toEnd half)))))
      Linear _ -> err . UnificationError $ "Can't force " ++ show n ++ " to be even"
      Full sm -> StrictMonoFun sm <$ demand0 (NumValue 0 (StrictMonoFun sm))
    evenGro (StrictMonoFun (StrictMono n mono)) = pure (StrictMonoFun (StrictMono (n - 1) mono))

    -- Check a numval is odd, and return its rounded down half
    oddGro :: Fun00 Z -> Checking (NumVal Z)
    oddGro (StrictMonoFun (StrictMono 0 mono)) = case mono of
      Linear (VPar (ExEnd out)) -> mkPred out >>= demandEven
      Linear _ -> err . UnificationError $ "Can't force " ++ show n ++ " to be even"
      -- full(n + 1) = 1 + 2 * full(n)
      -- hence, full(n) is the rounded down half
      Full sm -> nFull <$> demandSucc sm
    oddGro _ = err . UnificationError $ "Can't force " ++ show n ++ " to be even"

  -- Add dynamic logic to compute half of a variable.
  mkHalf :: OutPort -> Checking Src
  mkHalf out = do
    (_, [], [(const2,_)], _) <- next "const2" (Const (Num 2)) (S0, Some (Zy :* S0))
                                R0
                                (RPr ("value", TNat) R0)
    (_, [(lhs,_),(rhs,_)], [(half,_)], _) <- next "div2" (ArithNode Div) (S0, Some (Zy :* S0))
                                             (RPr ("left", TNat) (RPr ("right", TNat) R0))
                                             (RPr ("out", TNat) R0)
    wire (NamedPort out "numerator", TNat, lhs)
    wire (const2, TNat, rhs)
    req $ Define (toEnd out) (VNum (n2PowTimes 1 (nVar (VPar (toEnd half)))))
    pure half


  -- Add dynamic logic to compute the predecessor of a variable, and return that
  -- predecessor.
  -- The variable must be a non-zero nat!!
  mkPred :: OutPort -> Checking (NumVal Z)
  mkPred out = do
    (_, [], [(const1,_)], _) <- next "const1" (Const (Num 1)) (S0, Some (Zy :* S0))
                                R0
                                (RPr ("value", TNat) R0)
    (_, [(lhs,_),(rhs,_)], [(pred,_)], _) <- next "minus1" (ArithNode Sub) (S0, Some (Zy :* S0))
                                             (RPr ("left", TNat) (RPr ("right", TNat) R0))
                                             (RPr ("out", TNat) R0)
    wire (NamedPort out "", TNat, lhs)
    wire (const1, TNat, rhs)
    req $ Define (ExEnd out) (VNum (nPlus 1 (nVar (VPar (toEnd pred)))))
    pure (nVar (VPar (toEnd pred)))

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
