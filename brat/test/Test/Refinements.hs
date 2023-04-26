{-# LANGUAGE AllowAmbiguousTypes, FlexibleContexts #-}

module Test.Refinements where

import Brat.Checker
import Brat.Checker.Clauses.Refinements
import Brat.Checker.Helpers (binderToValue, defineSrc, uncons)
import Brat.Checker.Helpers.Nodes
import Brat.Checker.Monad
import Brat.Checker.Types
import Brat.Error
import Brat.FC hiding (end)
import Brat.Graph (Thing(..))
import Brat.Naming
import Brat.Syntax.Abstractor
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Bwd
import Test.Util
import Util

import Data.Bifunctor
import Data.Functor
import Test.Tasty
import Test.Tasty.HUnit

refine :: (DeBruijn (BinderType m), Show (BinderType m)) => Modey m -> Bwd End -> Refinement m
       -> (Int, Abstractor, [(PortName, BinderType m)], [(PortName, BinderType m)])
       -> Checking (Maybe (Abstractor, [(PortName, BinderType m)], [(PortName, BinderType m)]))
refine m ends ref (0, abs, (over:overs), unders) = let (pat, rest) = absUncons abs in
  ref pat ends over overs unders <&> fmap (helper rest)
 where
  helper rest (_, (Case (NA head) overs unders))
    = let NA abs = normaliseAbstractor (head :||: rest)
          (overs' :-> unders') = changeVars (ParToInx ends) 0 (doesItBind m) (overs :-> unders)
      in (abs, overs', unders')

  absUncons (APat p :||: rest) = (p, rest)
  absUncons (APat p) = (p, AEmpty)

refine m ends ref (n, a :||: b, o:os, us) = do
  let NA abs = normaliseAbstractor b
  result <- case (m, doesItBind m (snd o)) of
    (Braty, Just k) -> do
      (_, _, [(value, _)], _) <- next "" Hypo (B0,B0) [] [("value", Left k)]
      refine m (ends :< ExEnd (end value)) ref (n - 1, abs, os, us)
    _ -> refine m ends ref (n - 1, abs, os, us)
  pure $ case result of
    Just (abs, os, us) -> let NA abs' = normaliseAbstractor (a :||: abs) in
                            Just (abs', o:os, us)
    Nothing -> Nothing
refine _ _ _ (n, abs, _, _) = error $ show n ++ " " ++ show abs

refTest :: (DeBruijn (BinderType m), Show (BinderType m)) => Modey m
        -> Refinement m
        -> (Int, Abstractor, [(PortName, BinderType m)], [(PortName, BinderType m)])
        -> (Abstractor, [(PortName, BinderType m)], [(PortName, BinderType m)])
        -> Assertion
refTest m ref input (expAbs, expOvers, expUnders)
  = case runEmpty $ comp m ref input expOvers expUnders of
      Right (abs,_) -> abs @?= expAbs
      Left err -> assertFailure (showError err)
 where
  comp :: (DeBruijn (BinderType m), Show (BinderType m)) => Modey m -> Refinement m
       -> (Int, Abstractor, [(PortName, BinderType m)], [(PortName, BinderType m)])
       -> [(PortName, BinderType m)] -> [(PortName, BinderType m)] -> Checking Abstractor
  comp m ref input expOvers expUnders = localFC (FC (Pos 0 0) (Pos 0 0)) $ do
    refine m B0 ref input >>= \case
      Just (abs, overs, unders) -> typeEqRow m "" expOvers overs (B0,0) >>=
                                   typeEqRow m "" expUnders unders >>
                                   pure abs
      Nothing -> err $ UnreachableBranch

testZero = testCase "zero" $
           refTest Braty (refinementZero (Left Nat)) (0, abs, overs, []) (expAbs, expOvers, [])
 where
  abs = APat PZero :||: APat (Bind "xs")
  overs = [("n", Left Nat), ("xs", Right (TVec TBool (VApp (VInx 0) B0)))]

  expAbs = APat DontCare :||: APat (Bind "xs")
  expOvers = [("n", Left Nat), ("xs", Right (TVec TBool (VNum nZero)))]

testSucc = testCase "succ" $
           case runEmpty comp of
             Right _ -> pure ()
             Left err -> assertFailure (showError err)
 where
  comp = localFC (FC (Pos 0 0) (Pos 0 0)) $
    refine Braty B0 refinementSucc (0,abs,overs,[]) >>= \case
      Just (abs, overs, []) -> abs <$ do
        ty <- evTy (binderToValue Braty (snd (overs !! 1)))
        case uncons Braty ty of
          Just (TBool, TVec TBool n) -> pure ()
          Just x -> err $ TypeErr $ show x
          Nothing -> err (TypeErr "Can't uncons")

  abs = APat (POnePlus (Bind "n")) :||: APat (PCons (Bind "x") (Bind "xs"))
  overs = [("n", Left Nat), ("xs", Right (TVec TBool (VApp (VInx 0) B0)))]

  expAbs = APat (Bind "n") :||: APat (PCons (Bind "x") (Bind "xs"))

testNil = testCase "nil" $
          refTest Kerny (refinementNil Kerny) (0,abs,overs,[]) (expAbs,expOvers,[])
 where
  abs = APat (Bind "x")
  expAbs = APat DontCare

  overs = [("xs", Of Bit (VNum (nPlus 1 nZero)))]
  expOvers = [("xs", Of Bit (VNum nZero))]

testCons = testCase "cons" $
           refTest Braty (refinementCons Braty) (1,abs,overs,[]) (expAbs,expOvers,[])
 where
  abs = APat (Bind "n") :||: APat (PCons (Bind "x") (Bind "xs"))
  expAbs = APat (Bind "n") :||: (APat DontCare :||: (APat (Bind "x") :||: APat (Bind "xs")))

  overs = [("n", Left Nat), ("xs", Right $ TVec TBool (VNum (nPlus 1 nZero)))]
  expOvers = [("n", Left Nat), ("xs", Right $ TVec TBool (VNum (nPlus 1 nZero))), ("xs.head", Right TBool), ("xs.tail", Right $ TVec TBool (VNum nZero))]

testZeroOuts = testCase "zero_outs" $
               refTest Braty (refinementZero (Left Nat)) (0,abs,overs,unders) (expAbs,expOvers,expUnders)
 where
  abs = APat (Bind "n") :||: APat (Bind "X")
  expAbs = APat DontCare :||: APat (Bind "X")

  overs = [("n", Left Nat), ("X", Left (Star []))]
  unders = [("out", Right (TVec (VApp (VInx 0) B0) (VApp (VInx 1) B0)))]

  expOvers = [("n", Left Nat), ("X", Left (Star []))]
  expUnders = [("out", Right (TVec (VApp (VInx 0) B0) (VNum nZero)))]

testEnds = testCase "Ends" $ case runEmpty comp of
  Right (actAbs,_) -> expAbs @?= actAbs
  Left err -> assertFailure (showError err)
 where
  comp = localFC (FC (Pos 0 0) (Pos 0 0)) $ do
    result <- refine Braty B0 (refinementZero (Left Nat)) (1, abs, overs, [])
    case result of
      Just (actAbs, ao:actOvers, []) -> do
        (_, _, [(dummy,_)], _)<- next "" Hypo (B0,B0) [] [("value", Left (Star []))]
        (eo:expOvers) <- pure expOvers
        -- typeEqRow needs to do some evaluation, because the current vector length
        -- in actOvers is (VPar ...), which needs resolved before it's compared to
        -- the expected value
        -- ... BUT evaluation will crash when it sees a VInx, because we're not
        -- passing any local context, so lets substitute the X to a dummy value
        -- in both the rows
        typeEqRow Braty ""
          (eo:(changeVars (InxToPar (B0 :< ExEnd (end dummy))) 0 (doesItBind Braty) expOvers))
          (ao:(changeVars (InxToPar (B0 :< ExEnd (end dummy))) 0 (doesItBind Braty) actOvers))
           (B0, 0)
        pure actAbs
      Nothing -> err UnreachableBranch

  abs = APat (Bind "X") :||: (APat (Lit (Num 0)) :||: (APat (Bind "xs")))
  expAbs = APat (Bind "X") :||: (APat DontCare :||: (APat (Bind "xs")))

  overs =    [("X", Left (Star [])), ("n", Left Nat), ("xs", Right (TVec (varVal (Star []) (VInx 1)) (varVal Nat (VInx 0))))]
  expOvers = [("X", Left (Star [])), ("n", Left Nat), ("xs", Right (TVec (varVal (Star []) (VInx 1)) (VNum nZero)))]

refinementTests = testGroup "Refinements" [testZero,testSucc,testNil,testCons,testZeroOuts,testEnds]
