{-# LANGUAGE OverloadedStrings #-}

module Test.Circuit.Common where

import Data.String (IsString(..))

import Brat.Graph
import Brat.Naming
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Common

instance IsString Name where
  fromString s = MkName [(s, 0)]

idGraph :: Graph' Term
idGraph = ([BratNode "main" ("src" :>>: "tgt") [] [("fun", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))]
           ,KernelNode "src" Source [] [("a", Q Qubit)]
           ,KernelNode "tgt" Target [("b", Q Qubit)] []
           ]
          ,[(("src", "a"), Left (Q Qubit), ("tgt", "b"))]
          )

id2Graph :: Graph' Term
id2Graph = ([KernelNode "id" (Prim "X") [("xq_in", Q Qubit)] [("xq_out", Q Qubit)]
            --,KernelNode "eval" (Eval "") testProcess
            ,BratNode "main" ("src" :>>: "tgt") [] [("fun"
                                                    , K
                                                      (R [("ina", Q Qubit),  ("inb", Q Qubit)])
                                                      (R [("outa", Q Qubit), ("outb", Q Qubit)]))]
            ,KernelNode "src" Source [] [("a", Q Qubit), ("b", Q Qubit)]
            ,KernelNode "tgt" Target [("a", Q Qubit), ("b", Q Qubit)] []
            ]
           ,[(("src", "a"), Left (Q Qubit), ("tgt", "a"))
            ,(("src", "b"), Left (Q Qubit), ("tgt", "b"))
            ]
           )

xGraph :: Graph' Term
xGraph = ([BratNode "tket.X" (Prim "tket.X") [("kernel", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))] []
          ,KernelNode "X" (Eval ("tket.X", "kernel")) [("a", Q Qubit)] [("b", Q Qubit)]
          ,BratNode "main" ("src" :>>: "tgt") [] [("fun", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))]
          ,KernelNode "src" Source [] [("a", Q Qubit)]
          ,KernelNode "tgt" Target [("b", Q Qubit)] []
          ]
         ,[(("src", "a"), Left (Q Qubit), ("X", "a"))
          ,(("X", "b"), Left (Q Qubit), ("tgt", "b"))
          ]
         )

-- TODO:
rxGraph :: Graph' Term
rxGraph = ([BratNode "id" (Prim "Rx")
            [("th", SimpleTy FloatTy)]
            [("kernel", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))]
           ,BratNode "angle" (Prim "angle") [("th", SimpleTy FloatTy)] []
           --,KernelNode "eval" (Eval "") testProcess
           ,BratNode "main" ("src" :>>: "tgt") [] [("fun", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))]
           ,KernelNode "src" Source [] [("a", Q Qubit)]
           ,KernelNode "tgt" Target [("b", Q Qubit)] []
           ]
          ,[]
          )
