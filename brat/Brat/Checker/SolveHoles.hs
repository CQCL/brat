module Brat.Checker.SolveHoles (typeEq, buildNatVal, buildNum, invertNatVal) where

import Brat.Checker.Monad
import Brat.Checker.Types (kindForMode)
import Brat.Checker.Helpers (buildArithOp, buildConst, next)
import Brat.Error (ErrorMsg(..))
import Brat.Eval
import Brat.Graph (NodeType(..))
import Brat.Syntax.Common
import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.Syntax.Value
import Control.Monad.Freer
import Bwd
import Hasochism
import Util (zip_same_length)

import Control.Monad (filterM, unless, (>=>))
import Data.Foldable (traverse_)
import Data.Functor
import Data.Maybe (catMaybes)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Type.Equality (TestEquality(..), (:~:)(..))

-- Demand that two things are equal, we're allowed to solve variables in the
-- hope set to make this true.
-- Raises a user error if the vals cannot be made equal.
typeEq :: String -- String representation of the term for error reporting
       -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
       -> TypeKind -- The kind we're comparing at
       -> Val n -- Expected
       -> Val n -- Actual
       -> Checking ()
typeEq str stuff@(_ny :* _ks :* sems) k exp act = do
  hopes <- req AskHopeSet
  exp <- sem sems exp
  act <- sem sems act
  typeEqEta str stuff hopes k exp act

isNumVar :: Sem -> Maybe SVar
isNumVar (SNum (NumValue 0 (StrictMonoFun (StrictMono 0 (Linear v))))) = Just v
isNumVar _ = Nothing

-- Presumes that the hope set and the two `Sem`s are up to date.
typeEqEta :: String -- String representation of the term for error reporting
          -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n
          -> HopeSet -- The hope set
          -> TypeKind -- The kind we're comparing at
          -> Sem -- Expected
          -> Sem -- Actual
          -> Checking ()
typeEqEta tm (lvy :* kz :* sems) hopeSet (TypeFor m ((_, k):ks)) exp act = do
  -- Higher kinded things
  let nextSem = semLvl lvy
  let xz = B0 :< nextSem
  exp <- applySem exp xz
  act <- applySem act xz
  typeEqEta tm (Sy lvy :* (kz :<< k) :* (sems :<< nextSem)) hopeSet (TypeFor m ks) exp act
-- Not higher kinded - check for flex terms
-- (We don't solve under binders for now, so we only consider Zy here)
-- "easy" flex cases
typeEqEta _tm (Zy :* _ks :* _sems) hopeSet k (SApp (SPar e) B0) act
  | M.member e hopeSet = solveHope k e act
typeEqEta _tm (Zy :* _ks :* _sems) hopeSet k exp (SApp (SPar e) B0)
  | M.member e hopeSet = solveHope k e exp
typeEqEta _ (Zy :* _ :* _) hopeSet Nat exp act
  | Just (SPar e) <- isNumVar exp, M.member e hopeSet = solveHope Nat e act
  | Just (SPar e) <- isNumVar act, M.member e hopeSet = solveHope Nat e exp
-- harder cases, neither is in the hopeSet, so we can't define it ourselves
typeEqEta tm stuff@(ny :* _ks :* _sems) hopeSet k exp act = do
  exp <- quote ny exp
  act <- quote ny act
  let ends = catMaybes $ [exp,act] <&> getEnd
  unless (not $ any (flip M.member hopeSet) ends) $ typeErr "ends were in hopeset"
  filterM (isSkolem >=> pure . not) ends >>= \case
    [] -> typeEqRigid tm stuff k exp act -- easyish, both rigid i.e. already defined
    [e1, e2] | e1 == e2 -> pure () -- trivially same, even if they're both still yet-to-be-defined
    es -> -- tricky: must wait for one or other to become more defined
      mkYield "typeEqEta" (S.fromList es) >> typeEq tm stuff k exp act
 where
  getEnd (VApp (VPar e) _) = Just e
  getEnd (VNum n) = getNumVar n
  getEnd _ = Nothing

-- This will update the hopeSet, potentially invalidating things that have been eval'd
-- The Sem is closed, for now.
-- TODO: This needs to update the BRAT graph with the solution.
solveHope :: TypeKind -> End -> Sem -> Checking ()
solveHope k e v = quote Zy v >>= \v -> case doesntOccur e v of
  Right () -> defineEnd e v >> do
    dangling <- case (k, v) of
      (Nat, VNum v) -> buildNatVal v
      (Nat, _) -> err $ InternalError "Head of Nat wasn't a VNum"
      _ -> buildConst Unit TUnit
    let InEnd i = e
    req $ Wire (end dangling, kindType k, i)
    pure ()
  Left msg -> case v of
    VApp (VPar e') B0 | e == e' -> pure ()
    -- TODO: Not all occurrences are toxic. The end could be in an argument
    -- to a hoping variable which isn't used.
    -- E.g. h1 = h2 h1 - this is valid if h2 is the identity, or ignores h1.
    _ -> err msg

typeEqs :: String -> (Ny :* Stack Z TypeKind :* Stack Z Sem) n -> [TypeKind] -> [Val n] -> [Val n] -> Checking ()
typeEqs _ _ [] [] [] = pure ()
typeEqs tm stuff (k:ks) (exp:exps) (act:acts) = typeEqs tm stuff ks exps acts <* typeEq tm stuff k exp act
typeEqs _ _ _ _ _ = typeErr "arity mismatch"

typeEqRow :: Modey m
          -> String -- The term we complain about in errors
          -> (Ny :* Stack Z TypeKind :* Stack Z Sem) lv -- Next available level, the kinds of existing levels
          -> Ro m lv top0
          -> Ro m lv top1
          -> Either ErrorMsg (Some ((Ny :* Stack Z TypeKind :* Stack Z Sem) -- The new stack of kinds and fresh level
                                   :* (((:~:) top0) :* ((:~:) top1))) -- Proofs both input rows have same length (quantified over by Some)
                             ,[Checking ()] -- subproblems to run in parallel
                             )
typeEqRow _ _ stuff R0 R0 = pure (Some (stuff :* (Refl :* Refl)), [])
typeEqRow m tm stuff (RPr (_,ty1) ro1) (RPr (_,ty2) ro2) = typeEqRow m tm stuff ro1 ro2 <&> \(res, probs) -> (res, (typeEq tm stuff (kindForMode m) ty1 ty2):probs)
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
  else err $ TypeMismatch tm (show exp) (show act)
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
  traverse_ id probs -- uses Applicative (unlike sequence_ which uses Monad), hence parallelized
typeEqRigid tm lvkz (TypeFor _ []) (VSum m0 rs0) (VSum m1 rs1)
  | Just Refl <- testEquality m0 m1 = case zip_same_length rs0 rs1 of
      Nothing -> typeErr "Mismatched sum lengths"
      Just rs -> traverse eqVariant rs >>= (traverse_ id . concat)
 where
  eqVariant (Some r0, Some r1) = throwLeft $ (snd <$> typeEqRow m0 tm lvkz r0 r1)
typeEqRigid tm _ _ v0 v1 = err $ TypeMismatch tm (show v0) (show v1)

wire :: (Src, Val Z, Tgt) -> Checking ()
wire (src, ty, tgt) = req $ Wire (end src, ty, end tgt)

buildNum :: Integer -> Checking Src
buildNum n = buildConst (Num (fromIntegral n)) TNat


-- Generate wiring to produce a dynamic instance of the numval argument
buildNatVal :: NumVal (VVar Z) -> Checking Src
buildNatVal nv@(NumValue n gro) = case n of
  0 -> buildGro gro
  n -> do
    nDangling <- buildNum n
    ((lhs,rhs),out) <- buildArithOp Add
    src <- buildGro gro
    wire (nDangling, TNat, lhs)
    wire (src, TNat, rhs)
    pure out
 where
  buildGro :: Fun00 (VVar Z) -> Checking Src
  buildGro Constant0 = buildNum 0
  buildGro (StrictMonoFun sm) = buildSM sm

  buildSM :: StrictMono (VVar Z) -> Checking Src
  buildSM (StrictMono k mono) = do
    -- Calculate 2^k as `factor`
    two <- buildNum 2
    kDangling <- buildNum k
    ((lhs,rhs),factor) <- buildArithOp Pow
    wire (two, TNat, lhs)
    wire (kDangling, TNat, rhs)
    -- Multiply mono by 2^k
    ((lhs,rhs),out) <- buildArithOp Mul
    monoDangling <- buildMono mono
    wire (factor, TNat, lhs)
    wire (monoDangling, TNat, rhs)
    pure out

  buildMono :: Monotone (VVar Z) -> Checking Src
  buildMono (Linear (VPar (ExEnd e))) = pure $ NamedPort e "numval"
  buildMono (Full sm) = do
    -- Calculate 2^n as `outPlus1`
    two <- buildNum 2
    dangling <- buildSM sm
    ((lhs,rhs),outPlus1) <- buildArithOp Pow
    wire (two, TNat, lhs)
    wire (dangling, TNat, rhs)
    -- Then subtract 1
    one <- buildNum 1
    ((lhs,rhs),out) <- buildArithOp Sub
    wire (outPlus1, TNat, lhs)
    wire (one, TNat, rhs)
    pure out
  buildMono _ = err . InternalError $ "Trying to build a non-closed nat value: " ++ show nv

invertNatVal :: Tgt -> NumVal (VVar Z) -> Checking Tgt
invertNatVal tgt (NumValue up gro) = case up of
  0 -> invertGro tgt gro
  _ -> do
    ((lhs,rhs),out) <- buildArithOp Sub
    upSrc <- buildNum up
    wire (upSrc, TNat, rhs)
    wire (out, TNat, tgt)
    invertGro lhs gro
 where
  invertGro _ Constant0 = error "Invariant violated: the numval arg to invertNatVal should contain a variable"
  invertGro tgt (StrictMonoFun sm) = invertSM tgt sm

  invertSM tgt (StrictMono k mono) = case k of
    0 -> invertMono tgt mono
    _ -> do
      divisor <- buildNum (2 ^ k)
      ((lhs,rhs),out) <- buildArithOp Div
      wire (out, TNat, tgt)
      wire (divisor, TNat, rhs)
      invertMono lhs mono

  invertMono tgt (Linear (VPar (InEnd e))) = pure (NamedPort e "numval")
  invertMono tgt (Full sm) = do
    (_, [(llufTgt,_)], [(llufSrc,_)], _) <- next "luff" (Prim ("BRAT","lluf")) (S0, Some (Zy :* S0)) (REx ("n", Nat) R0) (REx ("n", Nat) R0)
    wire (llufSrc, TNat, tgt)
    invertSM llufTgt sm
