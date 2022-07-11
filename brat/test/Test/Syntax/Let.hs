{-# LANGUAGE OverloadedStrings #-}

module Test.Syntax.Let where

import Brat.Checker
import Brat.FC
import Brat.Load
import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.UserName

import Data.String
import Test.Tasty.HUnit

instance IsString UserName where
  fromString = PrefixName []

instance IsString Abstractor where
  fromString = Bind

fc = FC (Pos 0 0) (Pos 0 0)
wfc = WC fc

test = testCase "let" $
  let num = wfc . Simple . Num
      tm = Let (wfc ("x" :||: "y")) (wfc (wfc (num 1 :|: num 2)
                                     ::: [("a", SimpleTy IntTy), ("b", SimpleTy IntTy)]))
           (wfc (Var "x"))
      conn = ((), ())
      nil = (emptyEnv, [], fc)
  in case fst <$> run nil (check Braty (wfc tm) conn) of
       Right ([(_, SimpleTy IntTy)], ((), ())) -> pure ()
       Right (outs, ((), ())) -> assertFailure (show outs)
       x -> assertFailure (show x)

letTests = test
