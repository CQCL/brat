{-# LANGUAGE OverloadedStrings #-}

module Test.Circuit.Common where

import Control.Arrow ((&&&))
import Control.Monad.Except (runExceptT)
import qualified Data.Map as M
import Data.Tuple.HT
import Data.String (IsString(..))
import Test.Tasty.HUnit

import Brat.Graph
import Brat.Load (loadFiles)
import Brat.Naming
import Brat.Syntax.Core
import Brat.Syntax.Common

instance IsString Name where
  fromString s = MkName [(s, 0)]

idGraph :: Graph
idGraph = (M.fromList
           [("main_box", BratNode ("src" :>>: "tgt") [] [("fun", kty)])
           ,("main", BratNode Id [("a1", kty)] [("a1", kty)])
           ,("src", KernelNode Source [] [("a", Q Qubit)])
           ,("tgt", KernelNode Target [("b", Q Qubit)] [])
           ]
          ,[(("src", Ex, 0), Left (Q Qubit), ("tgt", In, 0))
           ,(("main_box", Ex, 0), Right kty, ("main", In, 0))
           ]
          )
 where
  kty = K (R [("a", Q Qubit)]) (R [("b", Q Qubit)])

swapGraph :: Graph
swapGraph = (M.fromList
             [("main_box", BratNode ("src" :>>: "tgt") [] [("fun", kty)])
             ,("main", BratNode Id [("a1", kty)] [("a1", kty)])
             ,("src", KernelNode Source [] [("a", Q Qubit), ("b", Q Qubit)])
             ,("tgt", KernelNode Target [("b", Q Qubit), ("a", Q Qubit)] [])
             ]
            ,[(("src", Ex, 0), Left (Q Qubit), ("tgt", In, 1))
             ,(("src", Ex, 1), Left (Q Qubit), ("tgt", In, 0))
             ,(("main_box", Ex, 0), Right kty, ("main", In, 0))
             ]
            )
 where
  kty = K
        (R [("a", Q Qubit),  ("b", Q Qubit)])
        (R [("b", Q Qubit), ("a", Q Qubit)])

xGraph :: Graph
xGraph = (M.fromList
          [("tket.X", BratNode (Prim "tket.X") [] [("a1", xTy)])
          ,("main_box", BratNode ("src" :>>: "tgt") [] [("fun", mainTy)])
          ,("X", KernelNode (Eval (("tket.X", Ex, 0), "_0")) [("xa", Q Qubit)] [("xb", Q Qubit)])
          ,("main", BratNode Id [("a1", mainTy)] [("a1", mainTy)])
          ,("src", KernelNode Source [] [("a", Q Qubit)])
          ,("tgt", KernelNode Target [("b", Q Qubit)] [])
          ]
         ,[(("src", Ex, 0), Left (Q Qubit), ("X", In, 0))
          ,(("X", Ex, 0), Left (Q Qubit), ("tgt", In, 0))
          ,(("main_box", Ex, 0), Right mainTy, ("main", In, 0))
          ]
         )
 where
  xTy = K (R [("xa", Q Qubit)]) (R [("xb", Q Qubit)])
  mainTy = K (R [("a", Q Qubit)]) (R [("b", Q Qubit)])

-- TODO:
rxGraph :: Graph
rxGraph = (M.fromList
           [("id", BratNode (Prim "Rx")
            [("th", SimpleTy FloatTy)]
            [("kernel", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))])
           ,("angle", BratNode (Const (Float 30.0)) [("th", SimpleTy FloatTy)] [])
           --,KernelNode (Eval "") testProcess
           ,("main", BratNode ("src" :>>: "tgt") [] [("fun", K (R [("a", Q Qubit)]) (R [("b", Q Qubit)]))])
           ,("src", KernelNode Source [] [("a", Q Qubit)])
           ,("tgt", KernelNode Target [("b", Q Qubit)] [])
           ]
          ,[]
          )

int = SimpleTy IntTy

twoGraph :: Graph
twoGraph = (M.fromList
            [("add", BratNode (Prim "add") [] [("thunk", C ([("a", int), ("b", int)] :-> [("c", int)]))])
            ,("add_eval", BratNode (Eval (("add", Ex, 0), "thunk")) [("a", int), ("b", int)] [("c", int)])
            ,("1a", BratNode (Const (Num 1)) [] [("value", int)])
            ,("1b", BratNode (Const (Num 1)) [] [("value", int)])
            ,("one", BratNode Id [("n", int)] [("n", int)])
            ,("two", BratNode Id [("a1", int)] [("a1", int)])
            ]
           ,[(("1a", Ex, 0), Right int, ("one", In, 0))
            ,(("1b", Ex, 0), Right int, ("add_eval", In, 0))
            ,(("one", Ex, 0), Right int, ("add_eval", In, 1))
            ,(("add_eval", Ex, 0), Right int, ("two", In, 0))
            ]
           )

oneGraph :: Graph
oneGraph = (M.fromList
            [("1", BratNode (Const (Num 1)) [] [("value", int)])
            ,("one", BratNode Id [("n", int)] [("n", int)])
            ]
           ,[(("1", Ex, 0), Right int, ("one", In, 0))]
           )

addNGraph :: Graph
addNGraph
  = (M.fromList
     [("add", BratNode (Prim "add") [] [("thunk", C ([("a", int), ("b", int)] :-> [("c", int)]))])
     ,("add_eval", BratNode (Eval (("add", Ex, 0), "thunk")) [("a", int), ("b", int)] [("c", int)])
     ,("N", BratNode (Prim "N") [] [("value", int)])
     ,("addN_box", BratNode ("addN_src" :>>: "addN_tgt") [] [("value", addN_ty)])
     ,("addN_src", BratNode Source [] [("in", int)])
     ,("addN_tgt", BratNode Target [("out", int)] [])
     ,("addN_eval", BratNode (Eval (("addN_box", Ex, 0), "value")) [("in", int)] [("out", int)])
     ,("addN", BratNode Id [("thunk", addN_ty)] [("thunk", addN_ty)])
     ]
    ,[(("addN_src", Ex, 0), Right int, ("add_eval", In, 1))
     ,(("N", Ex, 0), Right int, ("add_eval", In, 0))
     ,(("add", Ex, 0), Right int, ("addN_tgt", In, 0))
     ]
    )
 where
  addN_ty = C ([("in", int)] :-> [("out", int)])

addNmainGraph :: Graph
addNmainGraph
  = (M.fromList
     [("add", BratNode (Prim "add") [("a", int), ("b", int)] [("c", int)])
     ,("N", BratNode (Prim "N") [] [("value", int)])
     ,("addN_box", BratNode ("addN_src" :>>: "addN_tgt") [] [("value", addN_ty)])
     ,("addN_src", BratNode Source [("in", int)] [("in", int)])
     ,("addN_tgt", BratNode Target [("out", int)] [("out", int)])
     ,("addN_eval", BratNode (Eval (("addN_box", Ex, 0), "value")) [("value", addN_ty), ("in", int)] [("out", int)])
     ,("addN", BratNode (Prim "addN") [("in", int)] [("out", int)])
     ,("1", BratNode (Const (Num 1)) [] [("value", int)])
     ]
    ,[(("addN_src", Ex, 0), Right int, ("add", In, 0))
     ,(("N", Ex, 0), Right int, ("add", In, 1))
     ,(("add", Ex, 0), Right int, ("addN_tgt", In, 0))
     ,(("addN_box", Ex, 0), Right addN_ty, ("addN_eval", In, 0))
     ]
    )
 where
  addN_ty = C ([("in", int)] :-> [("out", int)])

extGraph :: Graph
extGraph
 = (M.fromList [("add", BratNode (Prim "add") [] [("thunk", C ([("a", int), ("b", int)] :-> [("c", int)]))])]
   ,[]
   )

emptyGraph = (M.empty, [])

-- Test the "close-enough" "equality" of two graphs
(=?) :: Graph -- Actual
     -> Graph -- Expected
     -> Assertion
(ns, ws) =? (ns', ws') = nodeEq >> wireEq
 where
  wireEq :: Assertion
  wireEq = let (s1, s2) = (wireSet ws, wireSet ws')
           in assertEqual (unlines [show s1, show s2]) (M.empty) (M.difference s1 s2)

  wireSet :: [Wire] -> M.Map String Int
  wireSet ws = foldr (M.alter inc) M.empty (wireKey <$> ws)

  wireKey :: Wire -> String
  wireKey ((_,d,i), ty, (_,d',i')) = unwords [show (d,i), "--", show ty, "->", show (d',i')]

  nodeEq :: Assertion
  nodeEq = let (s1, s2) = (nodeSet (snd <$> M.toList ns), nodeSet (snd <$> M.toList ns'))
               pp = unlines . fmap show . M.toList
           in  assertEqual (unlines ["Actual:", pp s1, "Expected:", pp s2]) M.empty (M.difference s1 s2)

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
    Combo t     -> "combo_" ++ show t
    Constructor c -> "ctor_" ++ show c

  nodeKey :: Node -> String
  nodeKey (BratNode thing ins outs)
    = thingKey False thing ++ (unlines [show ins, show outs])
  nodeKey (KernelNode thing ins outs)
    = thingKey True thing ++ (unlines [show ins, show outs])

  nodeSet :: [Node] -> M.Map String Int
  nodeSet ns = foldr (M.alter inc) M.empty (nodeKey <$> ns)

runProg :: String -> String -> Graph -> Assertion
runProg name contents expected = do
  runExceptT (loadFiles "" name contents) >>= \case
    Right (_, _, _, g) -> g =? expected
    Left err -> assertFailure (show err)
