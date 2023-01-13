module Test.Substitution where

import Brat.Checker.Monad
import Brat.Checker.Types
import Brat.Error
import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Control.Monad.Freer

import Test.Checking (runEmpty)

import Data.Bifunctor
import Test.Tasty
import Test.Tasty.HUnit

node = fst (fresh "" root)

-- Comparing type equality for rows is only exposed via checking equality of function types
chk ss ts = typeEq "" (Star []) (VFun Braty B0 ([] :-> ss)) (VFun Braty B0 ([] :-> ts))

var v = VApp v B0

checkSigs :: Checking ([(PortName, BinderType Brat)], [(PortName, BinderType Brat)]) -> Assertion
checkSigs x = case runEmpty (x >>= \(ss, ts) -> chk ss ts) of
  Right _ -> pure ()
  Left e -> assertFailure (showError e)

-- Instantiate both x and n into
-- (xs :: Vec(x, n))
inst = testCase "instantiation" $ checkSigs $ do
  req $ Declare x (Star [])
  req $ Declare n Nat
  pure ([("xs", exp)],[("xs", act)])
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  exp = Right $ TVec (var (VPar x)) (var (VPar n))
  act = Right $ changeVar (InxToPar (B0 :< x :< n)) 0 $
        TVec (var (VInx 1)) (var (VInx 0))

-- a version of `inst` on a row with no binding
-- (xs :: Vec(x, n), ys :: Vec(x, n))
insts = testCase "instantiations" $ checkSigs $ do
  req $ Declare x (Star [])
  req $ Declare n Nat
  pure ([("xs", exp),("ys", exp)], act)
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  exp = Right $ TVec (var (VPar x)) (var (VPar n))
  act = changeVars (InxToPar (B0 :< x :< n)) 0 doesItBind2 $
        [("xs", Right $ TVec (var (VInx 1)) (var (VInx 0))), ("ys", Right $ TVec (var (VInx 1)) (var (VInx 0)))]

-- Substitution doesn't affect local bindings
localBinding = testCase "localBinding" $ checkSigs $ do
  req $ Declare x (Star [])
  req $ Declare n Nat
  pure (exp, act)
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  -- Assuming x and n have already been bound:
  -- (xs :: Vec(x, n), m :: #, ys :: Vec(x, m), zs :: Vec(x, n))
  exp = [("xs", Right $ TVec (var (VPar x)) (var (VPar n)))
        ,("m",  Left Nat)
        ,("ys", Right (TVec (var (VPar x)) (var (VInx 0))))
        ,("zs", Right $ TVec (var (VPar x)) (var (VPar n)))
        ]

  act = changeVars (InxToPar (B0 :< x :< n)) 0 doesItBind2 $
        [("xs", Right $ TVec (var (VInx 1)) (var (VInx 0)))
        ,("m", Left Nat)
        ,("ys", Right $ TVec (var (VInx 2)) (var (VInx 0)))
        ,("zs", Right $ TVec (var (VInx 2)) (var (VInx 1)))
        ]

-- subst and insert both act on this signature
sig = [("X", Left (Star []))
      ,("x5", Right (TVec (VApp (VInx 0) B0) (VNum (nConstant 5))))
      ,("n", Left Nat)
      ,("xn", Right (TVec (VApp (VInx 1) B0) (VApp (VInx 0) B0)))
      ]

-- Replace "X" with "Y" in sig
subst = testCase "subst" $ checkSigs (pure (exp, act))
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  inxd = changeVars (InxToPar (B0 :< x :< n)) 0 (doesItBind Braty) sig
  insd = let (x:rest) = inxd in (("Y",Left (Star [])):rest)
  act = changeVars (ParToInx (B0 :< x :< n)) 0 (doesItBind Braty) insd
  exp = let (x:rest) = sig in ("Y",Left (Star [])):rest

-- Insert "Y" into the middle of sig
insert = testCase "insert" $ checkSigs (pure (exp, act))
 where
  x = ExEnd (Ex node 0)
  n = ExEnd (Ex node 1)
  y = ExEnd (Ex node 2)
  inxd = changeVars (InxToPar (B0 :< x :< n)) 0 (doesItBind Braty) sig
  insd = let (x:rest) = inxd in (x:("Y",Left (Star [])):rest)
  act = changeVars (ParToInx (B0 :< x :< y :< n)) 0 (doesItBind Braty) insd
  exp = let (x:rest) = sig in x:("Y",Left (Star [])):rest

  chk [] = pure ()
  chk ((Left k, Left k'):rest) = case kindEq k k' of
    Left msg -> err msg
    Right _ -> chk rest
  chk ((Right s, Right t):rest) = typeEq "" (Star []) s t *> chk rest
  chk _ = typeErr ""

nullSubst = testCase "nullSubst" $
  case runEmpty test of
    Right _ -> if (show exp == show act)
               then pure ()
               else assertFailure $
                    unlines ["Lexical difference in terms:"
                            ,"Expected: " ++ show exp
                            ,"Actual: " ++ show act
                            ]
    Left e -> assertFailure (showError e)
 where
  test = typeEq "X -> [X,X]" (Star [("X", Star [])]) exp act 

  exp = VLam B0 (VCon (plain "cons") [var (VInx 0), VCon (plain "cons") [var (VInx 0), VCon (plain "nil") []]])
  act = changeVar (InxToPar B0) 0 exp

substitutionTests = testGroup "Substitution" [inst, insts, localBinding, subst, insert, nullSubst]
