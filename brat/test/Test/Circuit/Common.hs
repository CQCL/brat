{-# LANGUAGE OverloadedStrings #-}

module Test.Circuit.Common where

import qualified Data.Map as Map
import Data.String (IsString(..))
import Test.Tasty.HUnit

import Brat.Graph
import Brat.Naming
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Common

instance IsString Name where
  fromString s = MkName [(s, 0)]

idGraph :: Graph' Term
idGraph = ([BratNode "main_box" ("src" :>>: "tgt") [] [("fun", kty)]
           ,BratNode "main" Id [("a1", kty)] [("a1", kty)]
           ,KernelNode "src" Source [] [("a", Q Qubit)]
           ,KernelNode "tgt" Target [("b", Q Qubit)] []
           ]
          ,[(("src", "a"), Left (Q Qubit), ("tgt", "b"))
           ,(("main_box", "fun"), Right kty, ("main", "a1"))
           ]
          )
 where
  kty = K (R [("a", Q Qubit)]) (R [("b", Q Qubit)])

swapGraph :: Graph' Term
swapGraph = ([BratNode "main_box" ("src" :>>: "tgt") [] [("fun", kty)]
             ,BratNode "main" Id [("a1", kty)] [("a1", kty)]
             ,KernelNode "src" Source [] [("a", Q Qubit), ("b", Q Qubit)]
             ,KernelNode "tgt" Target [("b", Q Qubit), ("a", Q Qubit)] []
             ]
            ,[(("src", "a"), Left (Q Qubit), ("tgt", "a"))
             ,(("src", "b"), Left (Q Qubit), ("tgt", "b"))
             ,(("main_box", "fun"), Right kty, ("main", "a1"))
             ]
            )
 where
  kty = K
        (R [("a", Q Qubit),  ("b", Q Qubit)])
        (R [("b", Q Qubit), ("a", Q Qubit)])

xGraph :: Graph' Term
xGraph = ([BratNode "tket.X" (Prim "tket.X") [] [("a1", xTy)]
          ,KernelNode "X" (Eval ("tket.X", "a")) [("xa", Q Qubit)] [("xb", Q Qubit)]
          ,BratNode "main_box" ("src" :>>: "tgt") [] [("fun", mainTy)]
          ,BratNode "main" Id [("a1", mainTy)] [("a1", mainTy)]
          ,KernelNode "src" Source [] [("a", Q Qubit)]
          ,KernelNode "tgt" Target [("b", Q Qubit)] []
          ]
         ,[(("src", "a"), Left (Q Qubit), ("X", "xa"))
          ,(("X", "xb"), Left (Q Qubit), ("tgt", "b"))
          ,(("main_box", "fun"), Right mainTy, ("main", "a1"))
          ]
         )
 where
  xTy = K (R [("xa", Q Qubit)]) (R [("xb", Q Qubit)])
  mainTy = K (R [("a", Q Qubit)]) (R [("b", Q Qubit)])

-- TODO:
rxGraph :: Graph' Term
rxGraph = ([BratNode "id" (Prim "Rx")
            [("th", SimpleTy FloatTy)]
            [("kernel", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))]
           ,BratNode "angle" (Const (Float 30.0)) [("th", SimpleTy FloatTy)] []
           --,KernelNode "eval" (Eval "") testProcess
           ,BratNode "main" ("src" :>>: "tgt") [] [("fun", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))]
           ,KernelNode "src" Source [] [("a", Q Qubit)]
           ,KernelNode "tgt" Target [("b", Q Qubit)] []
           ]
          ,[]
          )

int = SimpleTy IntTy

twoGraph :: Graph' Term
twoGraph = ([BratNode "add" (Prim "add") [] [("thunk", C ([("a", int), ("b", int)] :-> [("c", int)]))]
            ,BratNode "add" (Eval ("add", "thunk")) [("a", int), ("b", int)] [("c", int)]
            ,BratNode "1a" (Const (Num 1)) [] [("value", int)]
            ,BratNode "1b" (Const (Num 1)) [] [("value", int)]
            ,BratNode "one" Id [("n", int)] [("n", int)]
            ,BratNode "two" Id [("a1", int)] [("a1", int)]
            ]
           ,[(("1a", "value"), Right int, ("one", "n"))
            ,(("1b", "value"), Right int, ("add", "a"))
            ,(("one", "n"), Right int, ("add", "b"))
            ,(("add", "c"), Right int, ("two", "a1"))
            ]
           )

oneGraph :: Graph' Term
oneGraph = ([BratNode "1" (Const (Num 1)) [] [("value", int)]
            ,BratNode "one" Id [("n", int)] [("n", int)]
            ]
           ,[(("1", "value"), Right int, ("one", "n"))]
           )

addNGraph :: Graph' Term
addNGraph
  = ([BratNode "add" (Prim "add") [] [("thunk", C ([("a", int), ("b", int)] :-> [("c", int)]))]
     ,BratNode "add_eval" (Eval ("add", "thunk")) [("a", int), ("b", int)] [("c", int)]
     ,BratNode "N" (Prim "N") [] [("value", int)]
     ,BratNode "addN_box" ("addN_src" :>>: "addN_tgt") [] [("value", addN_ty)]
     ,BratNode "addN_src" Source [("in", int)] [("in", int)]
     ,BratNode "addN_tgt" Target [("out", int)] [("out", int)]
     ,BratNode "addN_eval" (Eval ("addN_box", "value")) [("value", addN_ty), ("in", int)] [("out", int)]
     ,BratNode "addN" Id [("thunk", addN_ty)] [("thunk", addN_ty)]
     ]
    ,[(("addN_src", "in"), Right int, ("add_eval", "a"))
     ,(("N", "value"), Right int, ("add_eval", "b"))
     ,(("add", "c"), Right int, ("addN_tgt", "out"))
     ,(("addN_box", "value"), Right addN_ty, ("addN_eval", "value"))
     ]
    )
 where
  addN_ty = C ([("in", int)] :-> [("out", int)])

addN2Graph :: Graph' Term
addN2Graph
  = ([BratNode "add" (Prim "add") [("a", int), ("b", int)] [("c", int)]
     ,BratNode "N" (Prim "N") [] [("value", int)]
     ,BratNode "addN_box" ("addN_src" :>>: "addN_tgt") [] [("value", addN_ty)]
     ,BratNode "addN_src" Source [("in", int)] [("in", int)]
     ,BratNode "addN_tgt" Target [("out", int)] [("out", int)]
     ,BratNode "addN_eval" (Eval ("addN_box", "value")) [("value", addN_ty), ("in", int)] [("out", int)]
     ,BratNode "addN" (Prim "addN") [("in", int)] [("out", int)]
     ,BratNode "1" (Const (Num 1)) [] [("value", int)]
     ]
    ,[(("addN_src", "in"), Right int, ("add", "a"))
     ,(("N", "value"), Right int, ("add", "b"))
     ,(("add", "c"), Right int, ("addN_tgt", "out"))
     ,(("addN_box", "value"), Right addN_ty, ("addN_eval", "value"))
     ]
    )
 where
  addN_ty = C ([("in", int)] :-> [("out", int)])

extGraph :: Graph' Term
extGraph
 = ([BratNode "add" (Prim "add") [] [("thunk", C ([("a", int), ("b", int)] :-> [("c", int)]))]]
   ,[]
   )

emptyGraph = ([], [])

-- Test the "close-enough" "equality" of two graphs
(=?) :: Graph' Term -> Graph' Term -> Assertion
(ns, ws) =? (ns', ws') = nodeEq >> wireEq
 where
  wireEq :: Assertion
  wireEq = let (s1, s2) = (wireSet ws, wireSet ws')
           in assertEqual (unlines [show s1, show s2]) (Map.empty) (Map.difference s1 s2)

  wireSet :: [Wire' Term] -> Map.Map String Int
  wireSet ws = foldr (Map.alter inc) Map.empty (wireKey <$> ws)

  wireKey :: Wire' Term -> String
  wireKey ((_, p), ty, (_, q)) = unwords [p, "--", show ty, "->", q]

  nodeEq :: Assertion
  nodeEq = let (s1, s2) = (nodeSet ns, nodeSet ns')
               pp = unlines . fmap show . Map.toList
           in  assertEqual (unlines ["Actual:", pp s1, "Expected:", pp s2]) Map.empty (Map.difference s1 s2)

  inc :: Maybe Int -> Maybe Int
  inc = Just . maybe 1 (1+)

  thingKey :: Bool -> Thing -> String
  thingKey k = (if k then ('k':) else id) . \case
    Prim x     -> "prim_" ++ x
    Const x    -> "const_" ++ show x
    Eval _     -> "eval"
    (_ :>>: _) -> "box"
    Source     -> "source"
    Target     -> "target"
    Id         -> "id"
    Hypo       -> "hypo"
    Combo _ _  -> "combo"

  nodeKey :: Node' Term -> String
  nodeKey (BratNode _ thing ins outs)
    = thingKey False thing ++ (unlines [show ins, show outs])
  nodeKey (KernelNode _ thing ins outs)
    = thingKey True thing ++ (unlines [show ins, show outs])

  nodeSet :: [Node' Term] -> Map.Map String Int
  nodeSet ns = foldr (Map.alter inc) Map.empty (nodeKey <$> ns)
