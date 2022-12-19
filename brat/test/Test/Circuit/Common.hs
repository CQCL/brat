{-# LANGUAGE OverloadedStrings #-}

module Test.Circuit.Common where

import Control.Arrow ((&&&))
import Control.Monad.Except (runExceptT)
import qualified Data.Map as M
import Data.Tuple.HT
import Data.String (IsString(..))
import Data.Foldable (fold)
import Test.Tasty.HUnit

import Brat.Graph
import Brat.Load (loadFiles)
import Brat.Naming
import Brat.Syntax.Core
import Brat.Syntax.Common
import Brat.Syntax.Simple

instance IsString Name where
  fromString s = MkName [(s, 0)]

idGraph :: Graph
idGraph = (M.fromList
           [("main_box", BratNode ("src" :>>: "tgt") [] [("fun", kty)])
           ,("main", BratNode Id [("a1", kty)] [("a1", kty)])
           ,("src", KernelNode Source [] [("a", Q Qubit)])
           ,("tgt", KernelNode Target [("b", Q Qubit)] [])
           ]
          ,[((Ex "src" 0), Left (Q Qubit), (In "tgt" 0))
           ,((Ex "main_box" 0), Right kty, (In "main" 0))
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
            ,[((Ex "src" 0), Left (Q Qubit), (In "tgt" 1))
             ,((Ex "src" 1), Left (Q Qubit), (In "tgt" 0))
             ,((Ex "main_box" 0), Right kty, (In "main" 0))
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
          ,("X", KernelNode (Eval (Ex "tket.X" 0)) [("xa", Q Qubit)] [("xb", Q Qubit)])
          ,("main", BratNode Id [("a1", mainTy)] [("a1", mainTy)])
          ,("src", KernelNode Source [] [("a", Q Qubit)])
          ,("tgt", KernelNode Target [("b", Q Qubit)] [])
          ]
         ,[((Ex "src" 0), Left (Q Qubit), (In "X" 0))
          ,((Ex "X" 0), Left (Q Qubit), (In "tgt" 0))
          ,((Ex "main_box" 0), Right mainTy, (In "main" 0))
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
            ,("add_eval", BratNode (Eval (Ex "add" 0)) [("a", int), ("b", int)] [("c", int)])
            ,("1a", BratNode (Const (Num 1)) [] [("value", int)])
            ,("1b", BratNode (Const (Num 1)) [] [("value", int)])
            ,("one", BratNode Id [("n", int)] [("n", int)])
            ,("two", BratNode Id [("a1", int)] [("a1", int)])
            ]
           ,[((Ex "1a" 0), Right int, (In "one" 0))
            ,((Ex "1b" 0), Right int, (In "add_eval" 0))
            ,((Ex "one" 0), Right int, (In "add_eval" 1))
            ,((Ex "add_eval" 0), Right int, (In "two" 0))
            ]
           )

oneGraph :: Graph
oneGraph = (M.fromList
            [("1", BratNode (Const (Num 1)) [] [("value", int)])
            ,("one", BratNode Id [("n", int)] [("n", int)])
            ]
           ,[((Ex "1" 0), Right int, (In "one" 0))]
           )

addNGraph :: String -> Graph
addNGraph port_name
  = (M.fromList
     [("add", BratNode (Prim "add") [] [(port_name, C ([("a", int), ("b", int)] :-> [("c", int)]))])
     ,("add_eval", BratNode (Eval (Ex "add" 0)) [("a", int), ("b", int)] [("c", int)])
     ,("N", BratNode (Prim "N") [] [("value", int)])
     ,("addN_box", BratNode ("addN_src" :>>: "addN_tgt") [] [("value", addN_ty)])
     ,("addN_src", BratNode Source [] [("inp", int)])
     ,("addN_tgt", BratNode Target [("out", int)] [])
     ,("addN", BratNode Id [("thunk", addN_ty)] [("thunk", addN_ty)])
     ]
    ,[((Ex "addN_src" 0), Right int, (In "add_eval" 1))
     ,((Ex "N" 0), Right int, (In "add_eval" 0))
     ,((Ex "add" 0), Right int, (In "addN_tgt" 0))
     ]
    )
 where
  addN_ty = C ([("inp", int)] :-> [("out", int)])

addNmainGraph :: Graph
addNmainGraph
  = (M.fromList
     [("add", BratNode (Prim "add") [("a", int), ("b", int)] [("c", int)])
     ,("N", BratNode (Prim "N") [] [("value", int)])
     ,("addN_box", BratNode ("addN_src" :>>: "addN_tgt") [] [("value", addN_ty)])
     ,("addN_src", BratNode Source [("inp", int)] [("inp", int)])
     ,("addN_tgt", BratNode Target [("out", int)] [("out", int)])
     ,("addN_eval", BratNode (Eval (Ex "addN_box" 0)) [("value", addN_ty), ("inp", int)] [("out", int)])
     ,("addN", BratNode (Prim "addN") [("inp", int)] [("out", int)])
     ,("1", BratNode (Const (Num 1)) [] [("value", int)])
     ]
    ,[((Ex "addN_src" 0), Right int, (In "add" 0))
     ,((Ex "N" 0), Right int, (In "add" 1))
     ,((Ex "add" 0), Right int, (In "addN_tgt" 0))
     ,((Ex "addN_box" 0), Right addN_ty, (In "addN_eval" 0))
     ]
    )
 where
  addN_ty = C ([("inp", int)] :-> [("out", int)])

extGraph :: Graph
extGraph
 = (M.fromList [("add", BratNode (Prim "add") [] [("thunk", C ([("a", int), ("b", int)] :-> [("c", int)]))])]
   ,[]
   )

-- Test the "close-enough" "equality" of two graphs
(=?) :: Graph -- Actual
     -> Graph -- Expected
     -> Assertion
(ns_act, ws_act) =? (ns_exp, ws_exp) = nodeEq >> wireEq
 where
  wireEq :: Assertion
  wireEq = assertNoDifference "Wires" (wireSet ws_act) (wireSet ws_exp)

  wireSet :: [Wire] -> M.Map String Int
  wireSet ws = foldr (M.alter inc) M.empty (wireKey <$> ws)

  wireKey :: Wire -> String
  wireKey (Ex _ p, ty, In _ p') = unwords [show p, "--", show ty, "->", show p']

  nodeEq :: Assertion
  nodeEq = assertNoDifference "Nodes" (nodeSet ns_act) (nodeSet ns_exp)

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

  nodeSet :: M.Map k Node -> M.Map String Int
  nodeSet ns = foldr (M.alter inc) M.empty (nodeKey <$> (snd <$> M.toList ns))

  -- `M.difference a b` finds things that are in `a` but not in `b`
  assertNoDifference :: String -> M.Map String Int -> M.Map String Int -> Assertion -- Actual vs Expected
  assertNoDifference msg act exp = case (M.difference act exp, M.difference exp act) of
    -- Extra wires in actual and expected maps
    (mAct, mExp)
      | M.null mAct, M.null mExp -> pure ()
      | M.null mAct -> assertFailure $ msg ++ " expected but not found: " ++ show mExp
      | M.null mExp -> assertFailure $ msg ++ " found but not expected: " ++ show mAct
      | otherwise -> assertFailure $ unlines [msg ++ "expected: " ++ show mExp
                                             ," but found: " ++ show mAct
                                             ]

runProg :: String -> String -> Graph -> Assertion
runProg name contents expected = do
  runExceptT (loadFiles "" name contents) >>= \case
    Right (_, _, _, named_gs) -> let gs = map snd named_gs in
      -- merge graphs from all functions
      (fold gs) =? expected
    Left err -> assertFailure (show err)
