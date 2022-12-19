{-# LANGUAGE OverloadedStrings #-}

module Test.Syntax.Let where

import Brat.Error (showError)
import Brat.Checker
import Brat.FC
import Brat.Load
import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.UserName
import Test.Checking (runEmpty)

import Data.String
import Test.Tasty.HUnit

instance IsString UserName where
  fromString = PrefixName []

instance IsString Abstractor where
  fromString = APat . Bind

fc = FC (Pos 0 0) (Pos 0 0)
wfc = WC fc

test = testCase "let" $
  let num = wfc . Simple . Num
      tm = Let (wfc ("x" :||: "y")) (wfc (wfc (num 1 :|: num 2)
                                     ::: [("a", SimpleTy IntTy), ("b", SimpleTy IntTy)]))
           (wfc (Var "x"))
      conn = ((), ())
  in case fst <$> runEmpty (let ?my = Braty in check (wfc tm) conn) of
       Right (((), [(_, SimpleTy IntTy)]), ((), ())) -> pure ()
       Right (((), outs), ((), ())) -> assertFailure (show outs)
       Left err -> assertFailure (showError err)

letTests = test
