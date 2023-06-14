module Test.Equality (eqTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure
import Test.Util

import Brat.Checker.Monad
import Brat.Checker.Types
import Brat.Syntax.Common
import Brat.Syntax.Value
import Bwd

-- Check that two indentical functions with a dangling de Bruijn index cause a
-- type mismatch when their embedded contexts are different
inequality = expectFail $ testCase "VFun.Inequality" $
             assertChecking $ typeEqRow my "" exp act eqctx
 where
  my = Braty
  exp = [("", Left (Star []))
        ,("", Right (VFun Braty ctx0 ([("", Right $ varVal (Star []) (VInx 0))] :-> [])))]
  act = [("", Left (Star []))
        ,("", Right (VFun Braty ctx1 ([("", Right $ varVal (Star []) (VInx 0))] :-> [])))]
  ctx0 = B0
  ctx1 = B0 :< TNat
  eqctx = ((B0,B0), 0)

-- Check that a VFun's dangling de Bruijn index gets evaluated by `eqRow` such
-- that it's considered equal to an equivalent first order type
equality = testCase "VFun.Equality" $
           assertChecking $ typeEqRow my "" exp act eqctx
 where
  my = Braty
  exp = [("", Left (Star []))
        ,("", Right (VFun Braty ctx0 ([("", Right $ varVal (Star []) (VInx 0))] :-> [])))]
  act = [("", Left (Star []))
        ,("", Right (VFun Braty ctx1 ([("", Right TNat)] :-> [])))]
  ctx0 = B0 :< TNat
  ctx1 = B0
  eqctx = ((B0,B0), 0)

eqTests = testGroup "Eq" [equality,inequality]
