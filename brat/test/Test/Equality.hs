module Test.Equality (eqTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure
import Test.Util

import Brat.Checker.Monad
import Brat.Checker.Types
import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.Eval (eqRow)
import Brat.FC (FC(..), Pos(..))
import Hasochism (N(..))

-- Check that two indentical functions with a dangling de Bruijn index cause a
-- type mismatch when their embedded contexts are different
inequality = testCase "VFun.Inequality" $
      case runEmpty $ localFC (FC (Pos 0 0) (Pos 0 0)) (eqRow "" Braty 0 exp act) of
            Right _ -> assertFailure "Should declare different"
            Left _ -> pure ()
 where
  exp :: Ro Brat Z (S Z)
  exp = REx ("", Star []) (S0 ::- RPr ("", expfn) R0)

  -- RPr type var refers to the type bound by `REx` in `exp`
  expfn :: Val (S Z)
  expfn = VFun Braty (RPr ("", varVal (Star []) (VInx VZ)) R0 :->> R0)

  act :: Ro Brat Z (S (S Z))
  act = REx ("", Star[]) ((S0 :<< TNat) ::- RPr ("", actfn) R0)

  -- RPr type var refers to the `TNat` at the end of the stash
  actfn :: Val (S (S Z))
  actfn = VFun Braty (RPr ("", varVal (Star []) (VInx (VS VZ))) R0 :->> R0)

-- Check that a VFun's dangling de Bruijn index is resolved by `eqRow`
-- to the enclosing stash such that it's considered equal to the same type inlined
equality1 = testCase "VFun.Equality1" $
           assertChecking $ eqRow "" Braty 0 exp act
 where
  exp :: Ro Brat Z (S (S Z))
  exp = REx ("", Star []) ((S0 :<< TNat) ::- RPr ("", expfn) R0)

  -- RPr type var refers to the 'TNat' in the stash in `exp`
  expfn :: Val (S (S Z))
  expfn = VFun Braty (RPr ("", varVal (Star []) (VInx (VS VZ))) R0 :->> R0)

  act :: Ro Brat Z (S Z)
  act = REx ("", Star []) (S0 ::- RPr ("", actfn) R0)
  -- no stash to refer to but we have TNat already:
  actfn = VFun Braty (RPr ("", TNat) R0 :->> R0)

equality2 = testCase "VFun.Equality2" $
            assertChecking $ eqRow "" Braty 0 exp exp_stash
 where
  -- type var refers to "a"
  exp :: Ro Brat Z (S (S Z))
  exp = REx ("a", Star []) (S0 ::-
            REx ("b", Star []) (S0 ::-
                  RPr ("", varVal (Star []) (VInx (VS VZ))) R0))

  -- type var still refers to "a", even tho index is different
  exp_stash :: Ro Brat Z (S (S (S Z)))
  exp_stash = REx ("a", Star []) (S0 ::-
                  REx ("b", Star []) ((S0 :<< TNat) ::-
                      -- VInx (VS VZ) on line below would refer to the TNat on line above
                      RPr ("", varVal (Star []) (VInx (VS (VS VZ)))) R0))

eqTests = testGroup "Eq" [equality1, equality2, inequality]
