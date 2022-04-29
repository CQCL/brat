module Test.Naming (nameTests) where

import Brat.Naming

import Data.List (sort)
import Test.Tasty.HUnit
import Test.Tasty

nameOrdTest = testCase "Ord instance" $
  let inp = [MkName []
            ,MkName [("a", 0)]
            ,MkName [("a", 0), ("a", 1)]
            ,MkName [("b", 0)]
            ,MkName [("a", 1)]
            ,MkName [("a", 0), ("a", 0)]
            ]
      exp = [MkName []
            ,MkName [("a", 0)]
            ,MkName [("a", 0), ("a", 0)]
            ,MkName [("a", 0), ("a", 1)]
            ,MkName [("a", 1)]
            ,MkName [("b", 0)]
            ]
  in sort inp @?= exp

nameTests = testGroup "Name" [nameOrdTest]
