module Brat.Checker.SolvePatterns (argProblems, argProblemsWithLeftovers, solve) where

import Brat.Checker.Monad
import Brat.Checker.Helpers
import Brat.Checker.SolveHoles (buildNatVal, invertNatVal)
import Brat.Checker.Types (EndType(..))
import Brat.Constructors
import Brat.Constructors.Patterns
import Brat.Error
import Brat.Eval
import Brat.Graph (NodeType(..), PrimTest(..))
import Brat.Syntax.Abstractor
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Control.Monad.Freer
import Hasochism

import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.Functor ((<&>))
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Type.Equality ((:~:)(..), testEquality)
import Brat.Syntax.Port (toEnd)

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
          unifyNum (nConstant (fromIntegral n)) (nVar (VPar (ExEnd (end src))))
    (Braty, Right ty) -> do
      simpleCheck Braty ty tm
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
        -- This `relationToInner` is very sus - it doesn't do any wiring!
        Just (Just _, relationToInner) -> do
          (node, [], kids@[(dangling, _)], _) <- next "unpacked_nat" Hypo (S0, Some (Zy :* S0))
            R0 -- we don't need to wire the src in; we just need the inner stuff
            (REx ("inner", Nat) R0)
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
typeOfEnd my e = (req (TypeOf e) <&> fst) >>= \case
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
  -- Create a row of hypothetical kinds which contextualise the arguments to the
  -- constructor.
  -- These need to be Tgts because we don't know how to compute them dynamically/
  (_, _, _, stuff) <- next "type_args" Hypo (S0, Some (Zy :* S0)) patRo R0
  (node, _, patArgWires, _) <- let ?my = my in anext "val_args" Hypo stuff R0 argRo
  trackM ("Constructor " ++ show c ++ "; type " ++ show ty)
  case (snd stuff) of
    Some (_ :* patEnds) -> do
      trackM (show pats)
      trackM (show patEnds)
      -- Match the patterns for `c` against the ends of the Hypo node, to
      -- produce the terms that we're interested in
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
  eqTest "unify" k l r >>= \case
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

-- Solve a metavariable statically - don't do anything dynamic
-- Once a metavariable is solved, we expect to not see it again in a normal form.
instantiateMeta :: End -> Val Z -> Checking ()
instantiateMeta e val = do
  throwLeft (doesntOccur e val)
  defineEnd e val

-- Solve a Nat kinded metavariable. Unlike `instantiateMeta`, this function also
-- makes the dynamic wiring for a metavariable. This only needs to happen for
-- numbers because they have nontrivial runtime behaviour.
--
-- We assume that the caller has done the occurs check and rules out trivial equations.
solveNumMeta :: End -> NumVal (VVar Z) -> Checking ()
solveNumMeta e nv = case (e, vars nv) of
 -- Compute the thing that the rhs should be based on the src, and instantiate src to that
 (ExEnd src,  [VPar (InEnd _)]) -> do
   -- Compute the value of the `tgt` variable from the known `src` value by inverting nv
   tgtSrc <- invertNatVal nv
   defineSrc (NamedPort src "") (VNum (nVar (VPar (toEnd tgtSrc))))
   wire (NamedPort src "", TNat, tgtSrc)

 (ExEnd src, _) -> defineSrc (NamedPort src "") (VNum nv)

 -- Both targets, we need to create the thing that they both derive from
 (InEnd bigTgt, [VPar (InEnd weeTgt)]) -> do
   (_, [(idTgt, _)], [(idSrc, _)], _) <- anext "numval id" Id (S0, Some (Zy :* S0))
                                         (REx ("n", Nat) R0) (REx ("n", Nat) R0)
   defineSrc idSrc (VNum (nVar (VPar (toEnd idTgt))))
   defineTgt (NamedPort weeTgt "") (VNum (nVar (VPar (toEnd idSrc))))
   wire (idSrc, TNat, NamedPort weeTgt "")
   let nv' = fmap (const (VPar (toEnd idSrc))) nv
   bigSrc <- buildNatVal nv'
   defineTgt (NamedPort bigTgt "") (VNum nv')
   wire (bigSrc, TNat, NamedPort bigTgt "")

 -- RHS is constant or Src, wire it into tgt
 (InEnd tgt,  _) -> do
   src <- buildNatVal nv
   defineTgt (NamedPort tgt "") (VNum nv)
   wire (src, TNat, NamedPort tgt "")

 where
  vars :: NumVal a -> [a]
  vars = foldMap pure

-- Need to keep track of which way we're solving - which side is known/unknown
-- Things which are dynamically unknown must be Tgts - information flows from Srcs
-- ...But we don't need to do any wiring here, right?
unifyNum :: NumVal (VVar Z) -> NumVal (VVar Z) -> Checking ()
unifyNum (NumValue lup lgro) (NumValue rup rgro)
  | lup <= rup = lhsFun00 lgro (NumValue (rup - lup) rgro)
  | otherwise  = lhsFun00 rgro (NumValue (lup - rup) lgro)
 where
  lhsFun00 :: Fun00 (VVar Z) -> NumVal (VVar Z) -> Checking ()
  lhsFun00 Constant0 num = demand0 num
  lhsFun00 (StrictMonoFun sm) num = lhsStrictMono sm num

  lhsStrictMono :: StrictMono (VVar Z) -> NumVal (VVar Z) -> Checking ()
  lhsStrictMono (StrictMono 0 mono) num = lhsMono mono num
  lhsStrictMono (StrictMono n mono) num = do
    num <- demandEven num
    lhsStrictMono (StrictMono (n - 1) mono) num

  lhsMono :: Monotone (VVar Z) -> NumVal (VVar Z) -> Checking ()
  lhsMono (Linear v) (NumValue 0 (StrictMonoFun (StrictMono 0 (Linear v')))) | v == v' = pure ()
  lhsMono (Linear (VPar e)) num = throwLeft (doesntOccur e (VNum num)) *>
                                  solveNumMeta e num
  lhsMono (Full sm) (NumValue 0 (StrictMonoFun (StrictMono 0 (Full sm'))))
    = lhsStrictMono sm (NumValue 0 (StrictMonoFun sm'))
  lhsMono m@(Full _) (NumValue 0 gro) = lhsFun00 gro (NumValue 0 (StrictMonoFun (StrictMono 0 m)))
  lhsMono (Full sm) (NumValue up gro) = do
    smPred <- demandSucc sm
    unifyNum (n2PowTimes 1 (nFull smPred)) (NumValue (up - 1) gro)

  demand0 :: NumVal (VVar Z) -> Checking ()
  demand0 (NumValue 0 Constant0) = pure ()
  demand0 n@(NumValue 0 (StrictMonoFun (StrictMono _ mono))) = case mono of
    Linear (VPar e) -> solveNumMeta e (nConstant 0)
    Full sm -> demand0 (NumValue 0 (StrictMonoFun sm))
    _ -> err . UnificationError $ "Couldn't force " ++ show n ++ " to be 0"
  demand0 n = err . UnificationError $ "Couldn't force " ++ show n ++ " to be 0"

  -- Complain if a number isn't a successor, else return its predecessor
  demandSucc :: StrictMono (VVar Z) -> Checking (NumVal (VVar Z))
  --   2^k * x
  -- = 2^k * (y + 1)
  -- = 2^k + 2^k * y
  demandSucc (StrictMono _ (Linear (VPar (ExEnd _)))) = error "Todo..." {-do
    -- This is sus because we don't have any tgt?
    ySrc <- invertNatVal (NamedPort x "") (NumValue 1 (StrictMonoFun sm))
    let y = nVar (VPar (toEnd ySrc))
    solveNumMeta (ExEnd x) (nPlus 1 y)
    pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes k y
  -}

  demandSucc sm@(StrictMono k (Linear (VPar (InEnd weeEnd)))) = do
    bigEnd <- invertNatVal (NumValue 1 (StrictMonoFun sm))
    solveNumMeta (toEnd bigEnd) (NumValue 0 (StrictMonoFun sm))
    pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes k (nVar (VPar (InEnd weeEnd)))

  --   2^k * full(n + 1)
  -- = 2^k * (1 + 2 * full(n))
  -- = 2^k + 2^(k + 1) * full(n)
  demandSucc (StrictMono k (Full nPlus1)) = do
    n <- demandSucc nPlus1
    pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes (k + 1) $ nFull n
  demandSucc n = err . UnificationError $ "Couldn't force " ++ show n ++ " to be a successor"

  -- Complain if a number isn't even, otherwise return half
  demandEven :: NumVal (VVar Z) -> Checking (NumVal (VVar Z))
  demandEven n@(NumValue up gro) = case up `divMod` 2 of
    (up, 0) -> NumValue up <$> evenGro gro
    (up, 1) -> nPlus (up + 1) <$> oddGro gro
   where
    evenGro :: Fun00 (VVar Z) -> Checking (Fun00 (VVar Z))
    evenGro Constant0 = pure Constant0
    evenGro (StrictMonoFun (StrictMono 0 mono)) = case mono of
      Linear (VPar (ExEnd out)) -> do
        half <- invertNatVal (NumValue 0 (StrictMonoFun (StrictMono 1 mono)))
        solveNumMeta (ExEnd out) (n2PowTimes 1 (nVar (VPar (toEnd half))))
        pure (StrictMonoFun (StrictMono 0 (Linear (VPar (toEnd half)))))
      Linear (VPar (InEnd tgt)) -> do
        halfTgt <- buildNatVal (NumValue 0 (StrictMonoFun (StrictMono 1 (Linear (VPar (toEnd tgt))))))
        let half = nVar (VPar (toEnd halfTgt))
        solveNumMeta (InEnd tgt) (n2PowTimes 1 half)
        pure (StrictMonoFun (StrictMono 0 (Linear (VPar (toEnd halfTgt)))))
      Full sm -> StrictMonoFun sm <$ demand0 (NumValue 0 (StrictMonoFun sm))
    evenGro (StrictMonoFun (StrictMono n mono)) = pure (StrictMonoFun (StrictMono (n - 1) mono))

    -- Check a numval is odd, and return its rounded down half
    oddGro :: Fun00 (VVar Z) -> Checking (NumVal (VVar Z))
    oddGro (StrictMonoFun (StrictMono 0 mono)) = case mono of
      Linear (VPar (ExEnd _)) -> do
        -- compute (/2) . (-1)
        doubTgt <- invertNatVal (NumValue 1 (StrictMonoFun (StrictMono 1 mono)))
        let [VPar (InEnd halfTgt)] = foldMap pure mono
        solveNumMeta (toEnd doubTgt) (nPlus 1 (n2PowTimes 1 (nVar (VPar (toEnd halfTgt)))))
        pure (nVar (VPar (toEnd halfTgt)))
      Linear (VPar (InEnd weeTgt)) -> do
        -- compute (/2) . (-1)
        bigTgt <- invertNatVal (NumValue 1 (StrictMonoFun (StrictMono 1 (Linear (VPar (toEnd weeTgt))))))
        let flooredHalf = nVar (VPar (toEnd weeTgt))
        solveNumMeta (toEnd bigTgt) (nPlus 1 (n2PowTimes 1 flooredHalf))
        pure flooredHalf

      -- full(n + 1) = 1 + 2 * full(n)
      -- hence, full(n) is the rounded down half
      Full sm -> nFull <$> demandSucc sm
    oddGro _ = err . UnificationError $ "Can't force " ++ show n ++ " to be even"

-- The variable must be a non-zero nat!!
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

numPatVal :: NumPat -> [End] -> (NumVal (VVar Z), [End])
numPatVal NPVar (e:es) = (nVar (VPar e), es)
numPatVal NP0 es = (nConstant 0, es)
numPatVal (NP1Plus np) es = case numPatVal np es of (nv, es) -> (nPlus 1 nv, es)
numPatVal (NP2Times np) es = case numPatVal np es of (nv, es) -> (n2PowTimes 1 nv, es)
numPatVal _ [] = error "Constructor table has an error (numPat)"

argProblems :: [Src] -> NormalisedAbstractor -> Problem -> Checking Problem
argProblems srcs na p = argProblemsWithLeftovers srcs na p >>= \case
  (p, []) -> pure p
  -- This isn't a problem in general, but I think it is when we call argProblems?
  _ -> err $ UnificationError "Pattern doesn't match expected length for constructor args"

argProblemsWithLeftovers :: [Src] -> NormalisedAbstractor -> Problem -> Checking (Problem, [Src])
argProblemsWithLeftovers srcs (NA (APull ps abs)) p = pullPorts portName show ps (map (, ()) srcs) >>= \srcs -> argProblemsWithLeftovers (fst <$> srcs) (NA abs) p
argProblemsWithLeftovers (src:srcs) na p | Just (pat, na) <- unconsNA na = first ((src, pat):) <$> argProblemsWithLeftovers srcs na p
argProblemsWithLeftovers srcs (NA AEmpty) p = pure (p, srcs)
argProblemsWithLeftovers [] abst _ = err $ NothingToBind (show abst)

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
