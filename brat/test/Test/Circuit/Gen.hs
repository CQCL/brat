{-# LANGUAGE OverloadedStrings #-}

module Test.Circuit.Gen (circuitTests) where

import Control.Monad.Identity
import Data.String(IsString(..))
import Test.Tasty
import Test.Tasty.HUnit

import Brat.Compile.Circuit
import Brat.Graph
import Brat.Naming
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Common
import Test.Circuit.Common

processTest :: Graph' Term -> (Row Term Quantum, Row Term Quantum) -> [Command] -> Assertion
processTest g io c = commands (process g io) @?= c

testId = testCase "id" $
         processTest idGraph (R [("in", Q Qubit)], R [("out", Q Qubit)]) []

testSwap = testCase "swap" $
  let sig = (R [("ina", Q Qubit), ("inb", Q Qubit)], R [("outb", Q Qubit), ("outa", Q Qubit)])
  in processTest swapGraph sig []

testX = testCase "X" $
        processTest xGraph (R [("in", Q Qubit)], R [("out", Q Qubit)]) [Cmd (Op "X" []) []]

-- TODO:
testRx = testCase "Rx" $
         processTest rxGraph (R [("in", Q Qubit)], R [("out", Q Qubit)]) [Cmd (Op "Rx" [{- angle?? -}]) []]

circuitTests = testGroup "Circuit" [testId, testX] -- not yet: testRx]
