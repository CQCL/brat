module Brat.Checker.SolveNumbers (unifyNum, NumUnifyMode(..)) where

import Brat.Checker.Monad
import Brat.Checker.Helpers
import Brat.Syntax.Value
import Brat.Syntax.Common
import Brat.Syntax.Port
import Brat.Error
import Brat.Eval
import Brat.Graph (NodeType(..))
import Hasochism
import Control.Monad.Freer

--import Debug.Trace
import qualified Data.Map as M

--trail = trace

-- This is currently lifted from SolvePatterns, which still imports it.
-- It is also used in SolveHoles, where it does the right mathematics
-- but the wrong wiring.

data NumUnifyMode = NUGinger | NUFred deriving (Show, Eq)
-- As Ginger Rogers said, "I do everything Fred does, only backwars in high heels.".


-- Solve a Nat kinded metavariable. Unlike `instantiateMeta`, this function also
-- makes the dynamic wiring for a metavariable. This only needs to happen for
-- numbers because they have nontrivial runtime behaviour.
--
-- We assume that the caller has done the occurs check and rules out trivial equations.
solveNumMeta :: End -> NumVal (VVar Z) -> Checking ()
solveNumMeta e nv = case (e, vars nv) of
 -- Compute the thing that the rhs should be based on the src, and instantiate src to that
 (ExEnd src,  [VPar (InEnd _tgt)]) -> do
   -- Compute the value of the `tgt` variable from the known `src` value by inverting nv
   tgtSrc <- invertNatVal nv
   instantiateMeta (ExEnd src) (VNum (nVar (VPar (toEnd tgtSrc))))
   wire (NamedPort src "", TNat, tgtSrc)

 (ExEnd src, _) -> instantiateMeta (ExEnd src) (VNum nv)

 -- Both targets, we need to create the thing that they both derive from
 (InEnd bigTgt, [VPar (InEnd weeTgt)]) -> do
   (_, [(idTgt, _)], [(idSrc, _)], _) <- anext "numval id" Id (S0, Some (Zy :* S0))
                                         (REx ("n", Nat) R0) (REx ("n", Nat) R0)
   defineSrc idSrc (VNum (nVar (VPar (toEnd idTgt))))
   instantiateMeta (InEnd weeTgt) (VNum (nVar (VPar (toEnd idSrc))))
   wire (idSrc, TNat, NamedPort weeTgt "")
   let nv' = fmap (const (VPar (toEnd idSrc))) nv -- weeTgt is the only thing to replace
   bigSrc <- buildNatVal nv'
   instantiateMeta (InEnd bigTgt) (VNum nv')
   wire (bigSrc, TNat, NamedPort bigTgt "")

 -- RHS is constant or Src, wire it into tgt
 (InEnd tgt,  _) -> do
   hopes <- req AskHopes
   src <- buildNatVal nv
   instantiateMeta (InEnd tgt) (VNum nv)
   if M.member tgt hopes then req (RemoveHope tgt) else pure ()
   wire (src, TNat, NamedPort tgt "")
 where
  vars :: NumVal a -> [a]
  vars = foldMap pure

-- Need to keep track of which way we're solving - which side is known/unknown
-- Things which are dynamically unknown must be Tgts - information flows from Srcs
-- ...But we don't need to do any wiring here, right?
unifyNum :: NumUnifyMode -> NumVal (VVar Z) -> NumVal (VVar Z) -> Checking ()
unifyNum numo (NumValue lup lgro) (NumValue rup rgro)
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
    unifyNum numo (n2PowTimes 1 (nFull smPred)) (NumValue (up - 1) gro)

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
  demandSucc (StrictMono k (Linear (VPar (ExEnd x)))) = do
      (_, [(yTgt, _)], [(ySrc, _)], _) <-
	next "yId" Id (S0, Some (Zy :* S0)) (REx ("value", Nat) R0) (REx ("value", Nat) R0)

      defineSrc ySrc (VNum (nVar (VPar (toEnd yTgt))))
      instantiateMeta (ExEnd x) (VNum (nPlus 1 (nVar (VPar (toEnd yTgt)))))
      pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes k (nVar (VPar (toEnd ySrc)))
      --   2^k * x
      -- = 2^k * (y + 1)
      -- = 2^k + 2^k * y
      -- Hence, the predecessor is (2^k - 1) + (2^k * y)
    
  demandSucc (StrictMono k (Linear (VPar (InEnd x)))) = case numo of
    NUGinger -> do
      (_, [(y,_)], _, _) <- anext "y" Hypo (S0, Some (Zy :* S0)) (REx ("", Nat) R0) R0
      yPlus1 <- invertNatVal (nPlus 1 (nVar (VPar (toEnd y))))
      solveNumMeta (InEnd x) (nVar (VPar (toEnd yPlus1)))
      pure $ nPlus ((2 ^ k) - 1) $ n2PowTimes k (nVar (VPar (toEnd y)))
    NUFred -> do
      hopes <- req AskHopes
      if not $ M.member x hopes then typeErr $ "Goodbye Fred!" else do
        (tgt, src) <- buildAdd 1
	fc <- req AskFC
	req (ANewHope (end tgt) fc)
	solveHopeVal Nat x (VNum (nVar (VPar (toEnd src))))
	pure (nVar (VPar (toEnd tgt)))

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
        (_, [], [(halfSrc, _)], _) <-
          next "half" Hypo (S0, Some (Zy :* S0)) R0 (REx ("value", Nat) R0)
        solveNumMeta (ExEnd out) (n2PowTimes 1 (nVar (VPar (toEnd halfSrc))))
        pure (StrictMonoFun (StrictMono 0 (Linear (VPar (toEnd halfSrc)))))
      Linear (VPar (InEnd tgt)) -> do
        halfTgt <- invertNatVal (NumValue 0 (StrictMonoFun (StrictMono 1 mono)))
        let half = nVar (VPar (toEnd halfTgt))
        solveNumMeta (InEnd tgt) (n2PowTimes 1 half)
        pure (StrictMonoFun (StrictMono 0 (Linear (VPar (toEnd halfTgt)))))
      Full sm -> StrictMonoFun sm <$ demand0 (NumValue 0 (StrictMonoFun sm))
    evenGro (StrictMonoFun (StrictMono n mono)) = pure (StrictMonoFun (StrictMono (n - 1) mono))

    -- Check a numval is odd, and return its rounded down half
    oddGro :: Fun00 (VVar Z) -> Checking (NumVal (VVar Z))
    oddGro (StrictMonoFun (StrictMono 0 mono)) = case mono of
      -- TODO: Why aren't we using `out`??
      Linear (VPar (ExEnd bubble)) -> do
        -- compute (/2) . (-1)
        (_, [], [(halfSrc,_)], _) <- next "floorHalf" Hypo (S0, Some (Zy :* S0)) R0 (REx ("value", Nat) R0)
        solveNumMeta (ExEnd bubble) (nPlus 1 (n2PowTimes 1 (nVar (VPar (toEnd halfSrc)))))
        pure (nVar (VPar (toEnd halfSrc)))
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
