module Brat.Checker.SolveHoles (typeEq) where

import Brat.Checker.Helpers (buildConst, buildNatVal)
import Brat.Checker.Monad
import Brat.Checker.Types (kindForMode)
import Brat.Error (ErrorMsg(..))
import Brat.Eval
import Brat.Syntax.Common
import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.Syntax.Value
import Control.Monad.Freer
import Bwd
import Hasochism
-- import Brat.Syntax.Port (toEnd)

import Control.Monad (when)
import Data.Bifunctor (second)
import Data.Foldable (sequenceA_)
import Data.Functor
import Data.Maybe (mapMaybe)
import qualified Data.Map as M
import Data.Type.Equality (TestEquality(..), (:~:)(..))

import Debug.Trace

trunk = trace

-- Demand that two closed values are equal, we're allowed to solve variables in the
-- hope set to make this true.
-- Raises a user error if the vals cannot be made equal.
typeEq :: String -- String representation of the term for error reporting
       -> TypeKind -- The kind we're comparing at
       -> Val Z -- Expected
       -> Val Z -- Actual
       -> Checking ()
typeEq str = typeEq' str (Zy :* S0 :* S0)


-- Internal version of typeEq with environment for non-closed values
typeEq' :: String -- String representation of the term for error reporting
        -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
        -> TypeKind -- The kind we're comparing at
        -> Val n -- Expected
        -> Val n -- Actual
        -> Checking ()
typeEq' str stuff@(_ny :* _ks :* sems) k exp act = do
  hopes <- req AskHopes
  exp <- sem sems exp
  act <- sem sems act
  trunk ("TYPEEQ' " ++ show exp ++ " =? " ++ show act) $ typeEqEta str stuff hopes k exp act

{-
isNumVar :: Sem -> Maybe SVar
isNumVar (SNum (NumValue 0 (StrictMonoFun (StrictMono 0 (Linear v))))) = Just v
isNumVar _ = Nothing
-}

natEq :: NumVal SVar -> NumVal SVar -> Checking ()
natEq i j | i == j = pure ()
natEq (NumValue lup lgro) (NumValue rup rgro)
  | lup <= rup = lhsFun00 lgro (NumValue (rup - lup) rgro)
  | otherwise  = lhsFun00 rgro (NumValue (lup - rup) lgro)
 where
  solveNumMeta :: End -> NumVal SVar -> Checking ()
  solveNumMeta e num = typeErr $ "SOLVENUMMETA " ++ show e ++ " " ++ show num

  lhsFun00 :: Fun00 SVar -> NumVal SVar -> Checking ()
  lhsFun00 Constant0 num = demand0 num
  lhsFun00 (StrictMonoFun sm) num = lhsStrictMono sm num

  lhsStrictMono :: StrictMono SVar -> NumVal SVar -> Checking ()
  lhsStrictMono (StrictMono 0 mono) num = lhsMono mono num
  lhsStrictMono (StrictMono n mono) num = do
    num <- demandEven num
    lhsStrictMono (StrictMono (n - 1) mono) num

  lhsMono :: Monotone SVar -> NumVal SVar -> Checking ()
  lhsMono (Linear v) (NumValue 0 (StrictMonoFun (StrictMono 0 (Linear v')))) | v == v' = pure ()
  lhsMono (Linear (SPar e)) num = -- throwLeft (doesntOccur e (SNum num)) *>
                                  solveNumMeta e num
  lhsMono (Full sm) (NumValue 0 (StrictMonoFun (StrictMono 0 (Full sm'))))
    = lhsStrictMono sm (NumValue 0 (StrictMonoFun sm'))
  lhsMono m@(Full _) (NumValue 0 gro) = lhsFun00 gro (NumValue 0 (StrictMonoFun (StrictMono 0 m)))
  lhsMono (Full sm) (NumValue up gro) = do
    smPred <- demandSucc sm
    natEq (n2PowTimes 1 (nFull smPred)) (NumValue (up - 1) gro)

  demand0 :: NumVal SVar -> Checking ()
  demand0 (NumValue 0 Constant0) = pure ()
  demand0 n@(NumValue 0 (StrictMonoFun (StrictMono _ mono))) = case mono of
    Linear (SPar e) -> solveNumMeta e (nConstant 0)
    Full sm -> demand0 (NumValue 0 (StrictMonoFun sm))
    _ -> err . UnificationError $ "Couldn't force " ++ show n ++ " to be 0"
  demand0 n = err . UnificationError $ "Couldn't force " ++ show n ++ " to be 0"

  -- Complain if a number isn't a successor, else return its predecessor
  demandSucc :: StrictMono SVar -> Checking (NumVal SVar)
  --   2^k * x
  -- = 2^k * (y + 1)
  -- = 2^k + 2^k * y
  demandSucc (StrictMono _{-k-} (Linear (SPar (ExEnd x)))) = do
    {-
    (_, [(yTgt, _)], [(ySrc, _)], _) <-
      next "yId" Id (S0, Some (Zy :* S0)) (REx ("value", Nat) R0) (REx ("value", Nat) R0)

    defineSrc ySrc (VNum (nVar (VPar (toEnd yTgt))))
    instantiateMeta (ExEnd x) (VNum (nPlus 1 (nVar (VPar (toEnd yTgt)))))
    pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes k (nVar (VPar (toEnd ySrc)))
    -}
    typeErr $ "DEMANDSUCC EX " ++ show x
  --   2^k * x
  -- = 2^k * (y + 1)
  -- = 2^k + 2^k * y
  -- Hence, the predecessor is (2^k - 1) + (2^k * y)
  demandSucc (StrictMono _{-k-} (Linear (SPar (InEnd x)))) = do
    {-
    (_, [(y,_)], _, _) <- anext "y" Hypo (S0, Some (Zy :* S0)) (REx ("", Nat) R0) R0
    yPlus1 <- invertNatVal (nPlus 1 (nVar (VPar (toEnd y))))
    solveNumMeta (InEnd x) (nVar (SPar (toEnd yPlus1)))
    pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes k (nVar (VPar (toEnd y)))
    -}
    typeErr $ "DEMANDSUCC IN " ++ show x

  --   2^k * full(n + 1)
  -- = 2^k * (1 + 2 * full(n))
  -- = 2^k + 2^(k + 1) * full(n)
  demandSucc (StrictMono k (Full nPlus1)) = do
    n <- demandSucc nPlus1
    pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes (k + 1) $ nFull n
  demandSucc n = err . UnificationError $ "Couldn't force " ++ show n ++ " to be a successor"

  -- Complain if a number isn't even, otherwise return half
  demandEven :: NumVal SVar -> Checking (NumVal SVar)
  demandEven n@(NumValue up gro) = case up `divMod` 2 of
    (up, 0) -> NumValue up <$> evenGro gro
    (up, 1) -> nPlus (up + 1) <$> oddGro gro
   where
    evenGro :: Fun00 SVar -> Checking (Fun00 SVar)
    evenGro Constant0 = pure Constant0
    evenGro (StrictMonoFun (StrictMono 0 mono)) = case mono of
      Linear (SPar (ExEnd out)) -> do
        {-
        (_, [], [(halfSrc, _)], _) <-
          next "half" Hypo (S0, Some (Zy :* S0)) R0 (REx ("value", Nat) R0)
        solveNumMeta (ExEnd out) (n2PowTimes 1 (nVar (VPar (toEnd halfSrc))))
        pure (StrictMonoFun (StrictMono 0 (Linear (VPar (toEnd halfSrc)))))
	-}
	typeErr $ "EVENGRO EX " ++ show out
      Linear (SPar (InEnd tgt)) -> do
        {-
        halfTgt <- invertNatVal (NumValue 0 (StrictMonoFun (StrictMono 1 mono)))
        let half = nVar (VPar (toEnd halfTgt))
        solveNumMeta (InEnd tgt) (n2PowTimes 1 half)
        pure (StrictMonoFun (StrictMono 0 (Linear (SPar (toEnd halfTgt)))))
	-}
	typeErr $ "EVENGRO IN " ++ show tgt
      Full sm -> StrictMonoFun sm <$ demand0 (NumValue 0 (StrictMonoFun sm))
    evenGro (StrictMonoFun (StrictMono n mono)) = pure (StrictMonoFun (StrictMono (n - 1) mono))

    -- Check a numval is odd, and return its rounded down half
    oddGro :: Fun00 SVar -> Checking (NumVal SVar)
    oddGro (StrictMonoFun (StrictMono 0 mono)) = case mono of
      -- TODO: Why aren't we using `out`??
      Linear (SPar (ExEnd bubble)) -> do
        -- compute (/2) . (-1)
	{-
        (_, [], [(halfSrc,_)], _) <- next "floorHalf" Hypo (S0, Some (Zy :* S0)) R0 (REx ("value", Nat) R0)
        solveNumMeta (ExEnd bubble) (nPlus 1 (n2PowTimes 1 (nVar (VPar (toEnd halfSrc)))))
        pure (nVar (VPar (toEnd halfSrc)))
	-}
	typeErr $ "ODDGRO EX " ++ show bubble
      Linear (SPar (InEnd weeTgt)) -> do
        -- compute (/2) . (-1)
	{-
        bigTgt <- invertNatVal (NumValue 1 (StrictMonoFun (StrictMono 1 (Linear (VPar (toEnd weeTgt))))))
        let flooredHalf = nVar (VPar (toEnd weeTgt))
        solveNumMeta (toEnd bigTgt) (nPlus 1 (n2PowTimes 1 flooredHalf))
        pure flooredHalf
	-}
	typeErr $ "ODDGRO IN " ++ show weeTgt

      -- full(n + 1) = 1 + 2 * full(n)
      -- hence, full(n) is the rounded down half
      Full sm -> nFull <$> demandSucc sm
    oddGro _ = err . UnificationError $ "Can't force " ++ show n ++ " to be even"




-- Presumes that the hope set and the two `Sem`s are up to date.
typeEqEta :: String -- String representation of the term for error reporting
          -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
          -> Hopes -- A map from the hope set to corresponding FCs
          -> TypeKind -- The kind we're comparing at
          -> Sem -- Expected
          -> Sem -- Actual
          -> Checking ()
typeEqEta tm (lvy :* kz :* sems) hopes (TypeFor m ((_, k):ks)) exp act = do
  -- Higher kinded things
  let nextSem = semLvl lvy
  let xz = B0 :< nextSem
  exp <- applySem exp xz
  act <- applySem act xz
  typeEqEta tm (Sy lvy :* (kz :<< k) :* (sems :<< nextSem)) hopes (TypeFor m ks) exp act
-- Not higher kinded - check for flex terms
-- (We don't solve under binders for now, so we only consider Zy here)
-- 1. "easy" flex cases
typeEqEta _tm (Zy :* _ks :* _sems) hopes k (SApp (SPar (InEnd e)) B0) act
  | M.member e hopes = solveHope k e act
typeEqEta _tm (Zy :* _ks :* _sems) hopes k exp (SApp (SPar (InEnd e)) B0)
  | M.member e hopes = solveHope k e exp
typeEqEta _ (Zy :* _ :* _) _ {-hopes-} Nat (SNum exp) (SNum act) = natEq exp act
  {-
  | Just (SPar (InEnd e)) <- isNumVar exp, M.member e hopes = solveHope Nat e act
  | Just (SPar (InEnd e)) <- isNumVar act, M.member e hopes = solveHope Nat e exp
  -}
-- 2. harder cases, neither is in the hope set, so we can't define it ourselves
typeEqEta tm stuff@(ny :* _ks :* _sems) hopes k exp act = do
  exp <- quote ny exp
  act <- quote ny act
  let ends = mapMaybe getEnd [exp,act]
  -- sanity check: we've already dealt with either end being in the hopeset
  when (or [M.member ie hopes | InEnd ie <- ends]) $ typeErr "ends were in hopeset"
  case ends of
    [] -> typeEqRigid tm stuff k exp act -- easyish, both rigid i.e. already defined
    -- variables are trivially the same, even if undefined, but the values may
    -- be different! E.g. X =? 1 + X
    [_, _] | exp == act -> pure ()
    -- TODO: Once we have scheduling, we must wait for one or the other to become more defined, rather than failing
    _  -> err (TypeMismatch tm (show exp) (show act))
 where
  getEnd (VApp (VPar e) _) = Just e
  getEnd (VNum n) = getNumVar n
  getEnd _ = Nothing

-- This will update the `hopes`, potentially invalidating things that have
-- been eval'd.
-- The Sem is closed, for now.
solveHope :: TypeKind -> InPort -> Sem -> Checking ()
solveHope k hope v = quote Zy v >>= \v -> case doesntOccur (InEnd hope) v of
  Right () -> do
    defineEnd (InEnd hope) v
    dangling <- case (k, v) of
      (Nat, VNum v) -> buildNatVal v
      (Nat, _) -> err $ InternalError "Head of Nat wasn't a VNum"
      _ -> buildConst Unit TUnit
    req (Wire (end dangling, kindType k, hope))
    req (RemoveHope hope)
  Left msg -> case v of
    VApp (VPar (InEnd end)) B0 | hope == end -> pure ()
    -- TODO: Not all occurrences are toxic. The end could be in an argument
    -- to a hoping variable which isn't used.
    -- E.g. h1 = h2 h1 - this is valid if h2 is the identity, or ignores h1.
    _ -> err msg

typeEqs :: String -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n -> [TypeKind] -> [Val n] -> [Val n] -> Checking ()
typeEqs _ _ [] [] [] = pure ()
typeEqs tm stuff (k:ks) (exp:exps) (act:acts) = typeEqs tm stuff ks exps acts <* typeEq' tm stuff k exp act
typeEqs _ _ _ _ _ = typeErr "arity mismatch"

typeEqRow :: Modey m
          -> String -- The term we complain about in errors
          -> (Ny :* Stack Z TypeKind :* Stack Z Sem) lv -- Next available level, the kinds of existing levels
          -> Ro m lv top0
          -> Ro m lv top1
          -> Either ErrorMsg (Some ((Ny :* Stack Z TypeKind :* Stack Z Sem) -- The new stack of kinds and fresh level
                                   :* ((:~:) top0 :* (:~:) top1)) -- Proofs both input rows have same length (quantified over by Some)
                             ,[Checking ()] -- subproblems to run in parallel
                             )
typeEqRow _ _ stuff R0 R0 = pure (Some (stuff :* (Refl :* Refl)), [])
typeEqRow m tm stuff (RPr (_,ty1) ro1) (RPr (_,ty2) ro2) = typeEqRow m tm stuff ro1 ro2 <&> second
  ((:) (typeEq' tm stuff (kindForMode m) ty1 ty2))
typeEqRow m tm (ny :* kz :* semz) (REx (_,k1) ro1) (REx (_,k2) ro2) | k1 == k2 = typeEqRow m tm (Sy ny :* (kz :<< k1) :* (semz :<< semLvl ny)) ro1 ro2
typeEqRow _ _ _ _ _ = Left $ TypeErr "Mismatched rows"

-- Calls to typeEqRigid *must* start with rigid types to ensure termination
typeEqRigid :: String -- String representation of the term for error reporting
            -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
            -> TypeKind -- The kind we're comparing at
            -> Val n -- Expected
            -> Val n -- Actual
            -> Checking ()
typeEqRigid tm (_ :* _ :* semz) Nat exp act = do
  -- TODO: What if there's hope in the numbers?
  exp <- sem semz exp
  act <- sem semz act
  if getNum exp == getNum act
  then pure ()
  else trunk "HELLO TYPEEQRIGID TODO" $ err $ TypeMismatch tm ("TYPEEQRIGID " ++ show exp) ("TODO " ++ show act)
typeEqRigid tm stuff@(_ :* kz :* _) (TypeFor m []) (VApp f args) (VApp f' args') | f == f' =
  svKind f >>= \case
    TypeFor m' ks | m == m' -> typeEqs tm stuff (snd <$> ks) (args <>> []) (args' <>> [])
      -- pattern should always match
    _ -> err $ InternalError "quote gave a surprising result"
 where
  svKind (VPar e) = kindOf (VPar e)
  svKind (VInx n) = pure $ proj kz n
typeEqRigid tm lvkz (TypeFor m []) (VCon c args) (VCon c' args') | c == c' =
  req (TLup (m, c)) >>= \case
        Just ks -> typeEqs tm lvkz (snd <$> ks) args args'
        Nothing -> err $ TypeErr $ "Type constructor " ++ show c
                        ++ " undefined " ++ " at kind " ++ show (TypeFor m [])
typeEqRigid tm lvkz (Star []) (VFun m0 (ins0 :->> outs0)) (VFun m1 (ins1 :->> outs1)) | Just Refl <- testEquality m0 m1 = do
  probs :: [Checking ()] <- throwLeft $ typeEqRow m0 tm lvkz ins0 ins1 >>= \case -- this is in Either ErrorMsg
        (Some (lvkz :* (Refl :* Refl)), ps1) -> typeEqRow m0 tm lvkz outs0 outs1 <&> (ps1++) . snd
  sequenceA_ probs -- uses Applicative (unlike sequence_ which uses Monad), hence parallelized
typeEqRigid tm _ _ v0 v1 = err $ TypeMismatch tm (show v0) (show v1)
