{-# LANGUAGE OverloadedStrings #-}

module Test.Circuit where

import Control.Monad.Identity
import Data.String(IsString(..))
import Test.Tasty
import Test.Tasty.HUnit

import Brat.Compile.Circuit
import Brat.Graph
import Brat.Naming
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Common

instance IsString Name where
  fromString s = MkName [(s, 0)]

bump :: Name -> Name
bump (MkName ((s, i):ss)) = MkName ((s, i + 1):ss)

mkName :: String -> Name
mkName s = MkName [(s, 0)]

processTest :: Graph' Term -> (Row Term Quantum, Row Term Quantum) -> [Command] -> Assertion
processTest g io c = commands (process g io) @?= c

testId = testCase "id" $
  let g = ([KernelNode "id" (Prim "X") [("xq_in", Q Qubit)] [("xq_out", Q Qubit)]
           --,KernelNode "eval" (Eval "") testProcess
           ,BratNode "main" ("src" :>>: "tgt") [] [("fun", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))]
           ,KernelNode "src" Source [] [("a", Q Qubit)]
           ,KernelNode "tgt" Target [("b", Q Qubit)] []
           ]
          ,[(("src", "a"), Left (Q Qubit), ("tgt", "b"))]
          )
      c = [Cmd (Op "X" []) []]
  in processTest g (R [("in", Q Qubit)], R [("out", Q Qubit)]) c


circuitTests = testGroup "Circuit" [testId]
