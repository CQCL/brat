{-# LANGUAGE OverloadedStrings #-}

module Test.Circuit.Common where

import Control.Arrow ((&&&))
import Control.Monad.Except (runExceptT)
import qualified Data.Map as M
import Data.Tuple.HT
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import Data.String (IsString(..))
import Data.Foldable (fold)
import Data.Functor ((<&>))
import Test.Tasty.HUnit

import Brat.Graph
import Brat.Checker.Helpers (kindType)
import Brat.Load (loadFiles)
import Brat.Naming
import Brat.Syntax.Core
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName (plain)
import Bwd

instance IsString Name where
  fromString s = MkName [(s, 0)]

kernel cty = VFun Kerny B0 cty

idGraph :: Graph
idGraph = (M.fromList
           [("main_box", BratNode ("src" :>>: "tgt") [] [("thunk", kty)])
           ,("main", BratNode Id [("a1", kty)] [("a1", kty)])
           ,("src", KernelNode Source [] [("a", Q Qubit)])
           ,("tgt", KernelNode Target [("b", Q Qubit)] [])
           ,("kcr-main", BratNode Hypo [("a1", star_t)] []) -- into which to skindCheck the thunk type
           ]                                        -- (however skindCheck doesn't produce any nodes for that)
          ,[((Ex "src" 0), Left (Q Qubit), (In "tgt" 0))
           ,((Ex "main_box" 0), Right kty, (In "main" 0))
           ]
          )
 where
  kty = kernel ([("a", Q Qubit)] :-> [("b", Q Qubit)])

swapGraph :: Graph
swapGraph = (M.fromList
             [("main_box", BratNode ("src" :>>: "tgt") [] [("thunk", kty)])
             ,("main", BratNode Id [("a1", kty)] [("a1", kty)])
             ,("src", KernelNode Source [] [("a", Q Qubit), ("b", Q Qubit)])
             ,("tgt", KernelNode Target [("b", Q Qubit), ("a", Q Qubit)] [])
             ,("kcr-main", BratNode Hypo [("a1", star_t)] []) -- into which to skindCheck the thunk type
             ]
            ,[((Ex "src" 0), Left (Q Qubit), (In "tgt" 1))
             ,((Ex "src" 1), Left (Q Qubit), (In "tgt" 0))
             ,((Ex "main_box" 0), Right kty, (In "main" 0))
             ]
            )
 where
  kty = kernel
        ([("a", Q Qubit),  ("b", Q Qubit)] :-> [("b", Q Qubit), ("a", Q Qubit)])

xGraph :: Graph
xGraph = (M.fromList
          [("tket.X", BratNode (Prim "tket.X") [] [("a1", xTy)])
          ,("X", KernelNode (Eval (Ex "tket.X" 0)) [("xa", Q Qubit)] [("xb", Q Qubit)])
          ,("main_box", BratNode ("src" :>>: "tgt") [] [("thunk", mainTy)])
          ,("main", BratNode Id [("a1", mainTy)] [("a1", mainTy)])
          ,("src", KernelNode Source [] [("a", Q Qubit)])
          ,("tgt", KernelNode Target [("b", Q Qubit)] [])
          ,("kcr-X", BratNode Hypo [("a1", star_t)] []) -- these two receive the thunk types
          ,("kcr-main", BratNode Hypo [("a1", star_t)] [])
          ]
         ,[((Ex "src" 0), Left (Q Qubit), (In "X" 0))
          ,((Ex "X" 0), Left (Q Qubit), (In "tgt" 0))
          ,((Ex "main_box" 0), Right mainTy, (In "main" 0))
          ]
         )
 where
  xTy = kernel ([("xa", Q Qubit)] :-> [("xb", Q Qubit)])
  mainTy = kernel ([("a", Q Qubit)] :-> [("b", Q Qubit)])

-- TODO:
rxGraph :: Graph
rxGraph = (M.fromList
           [("id", BratNode (Prim "Rx")
            [("th", TFloat)]
            [("kernel", kernel ([("a", Q Qubit)] :-> [("b", Q Qubit)]))])
           ,("angle", BratNode (Const (Float 30.0)) [("th", TFloat)] [])
           --,KernelNode (Eval "") testProcess
           ,("main", BratNode ("src" :>>: "tgt") [] [("thunk", kernel ([("a", Q Qubit)] :-> [("b", Q Qubit)]))])
           ,("src", KernelNode Source [] [("a", Q Qubit)])
           ,("tgt", KernelNode Target [("b", Q Qubit)] [])
           ]
          ,[]
          )

int = TInt

twoGraph :: Graph
twoGraph = (M.fromList (
            [("add", BratNode (Prim "add") [] [("thunk", add_ty)])
            ,("add_eval", BratNode (Eval (Ex "add" 0)) [("a", int), ("b", int)] [("c", int)])
            ,("1a", BratNode (Const (Num 1)) [] [("value", int)])
            ,("1b", BratNode (Const (Num 1)) [] [("value", int)])
            ,("one", BratNode Id [("n", int)] [("n", int)])
            ,("two", BratNode Id [("a1", int)] [("a1", int)])
            ,("kcr-add", BratNode Hypo [("thunk", star_t)] [])
            ,("kcr-one", BratNode Hypo [("n", star_t)] [])
            ,("kcr-two", BratNode Hypo [("a1", star_t)] [])
            ,("kcr-cty", BratNode Hypo [("a", star_t), ("b", star_t), ("c", star_t)] [])
            ] ++ ints 5)
           ,[((Ex "1a" 0), Right int, (In "one" 0))
            ,((Ex "1b" 0), Right int, (In "add_eval" 0))
            ,((Ex "one" 0), Right int, (In "add_eval" 1))
            ,((Ex "add_eval" 0), Right int, (In "two" 0))
            --,(Ex "kcr-cty" 0, Right star_t, In "kcr-add" 0)
                -- no node exists to actually compute the function type. kcr-cty merely verifies
                -- that it is a well-formed type (by kindChecking its components, not putting them together)
            ,(Ex "int_1" 0, Right star_t, In "kcr-cty" 0)
            ,(Ex "int_2" 0, Right star_t, In "kcr-cty" 1)
            ,(Ex "int_3" 0, Right star_t, In "kcr-cty" 2)
            ,(Ex "int_4" 0, Right star_t, In "kcr-one" 0)
            ,(Ex "int_5" 0, Right star_t, In "kcr-two" 0)
            ]
           )
  where
    add_ty = VFun Braty B0 ([("a", Right int), ("b", Right int)] :-> [("c", Right int)])

oneGraph :: Graph
oneGraph = (M.fromList (
            [("1", BratNode (Const (Num 1)) [] [("value", int)])
            ,("one", BratNode Id [("n", int)] [("n", int)])
            ,("kcr", BratNode Hypo [("n", star_t)] [])
            ] ++ ints 1)
           ,[((Ex "1" 0), Right int, (In "one" 0))
            ,((Ex "int" 0), Right star_t, (In "kcr" 0))]
           )

star_t = kindType $ Star []
ints :: Int -> [(Name, Node)]
ints n = [int_node (fromString $ "int_" ++ show x) | x <- [1..n]]
int_node :: Name -> (Name, Node)
int_node n = (n, BratNode (Constructor $ plain "Int") [] [("value", star_t)])

addNGraph :: String -> Graph
addNGraph port_name
  = (M.fromList (
     [("add", BratNode (Prim "add") [] [(port_name, add_ty)])
     ,("add_eval", BratNode (Eval (Ex "addN_src" 1)) [("a", int), ("b", int)] [("c", int)])
     ,("N", BratNode (Prim "N") [] [("value", int)])
     ,("addN_box", BratNode ("addN_src" :>>: "addN_tgt") [(port_name, add_ty), ("value", int)] [("thunk", addN_ty)])
     ,("addN_src", BratNode Source [] [("inp", int), (port_name, add_ty), ("value", int)])
     ,("addN_tgt", BratNode Target [("out", int)] [])
     ,("addN", BratNode Id [("thunk", addN_ty)] [("thunk", addN_ty)])
     ,("kcr-n", BratNode Hypo [("value", star_t)] [])
     ,("kcr-add-ty", BratNode Hypo [("a", star_t), ("b", star_t), ("c", star_t)] [])
     ,("kcr-add", BratNode Hypo [(port_name, star_t)] []) -- in theory the thunk type wired in here; add is Ext => Anon => "a1"
     ,("kcr-addN-ty", BratNode Hypo [("inp", star_t), ("out", star_t)] [])
     ,("kcr-addN", BratNode Hypo [("thunk", star_t)] [])
     ] ++ ints 6)
    ,[(Ex "N" 0, Right int, In "addN_box" 1)
     ,(Ex "add" 0, Right add_ty, In "addN_box" 0)
     ,(Ex "addN_box" 0, Right addN_ty, In "addN" 0)
     ,((Ex "addN_src" 0), Right int, (In "add_eval" 0)) -- argument
     ,((Ex "addN_src" 2), Right int, (In "add_eval" 1)) -- captured
     ,((Ex "add_eval" 0), Right int, (In "addN_tgt" 0))
     ,(Ex "int_1" 0, Right star_t, In "kcr-n" 0)
     ,(Ex "int_2" 0, Right star_t, In "kcr-add-ty" 0)
     ,(Ex "int_3" 0, Right star_t, In "kcr-add-ty" 1)
     ,(Ex "int_4" 0, Right star_t, In "kcr-add-ty" 2)
     ,(Ex "int_5" 0, Right star_t, In "kcr-addN-ty" 0)
     ,(Ex "int_6" 0, Right star_t, In "kcr-addN-ty" 1)
     ]
    )
 where
  add_ty = VFun Braty B0 ([("a", Right int), ("b", Right int)] :-> [("c", Right int)])
  addN_ty = VFun Braty B0 ([("inp", Right int)] :-> [("out", Right int)])

addNmainGraph :: Graph
addNmainGraph =
  let (ns, ws) = addNGraph "thunk"
  in (M.fromList (
     (M.toList ns) ++
     [("addN_eval", BratNode (Eval (Ex "addN" 0)) [("inp", int)] [("out", int)])
     ,("1", BratNode (Const (Num 1)) [] [("value", int)])
     ,("main", BratNode Id [("a1", int)] [("a1", int)])
     ,("kcr-main", BratNode Hypo [("a1", star_t)] [])
     ] ++ [int_node "xtra_int"])
    ,ws ++ [
      (Ex "1" 0, Right int, In "addN_eval" 0)
     ,(Ex "addN_eval" 0, Right int, In "main" 0)
     ,(Ex "xtra_int" 0, Right star_t, In "kcr-main" 0)
     ]
    )
 where
  addN_ty = VFun Braty B0 ([("inp", Right TInt)] :-> [("out", Right TInt)])

extGraph :: Graph
extGraph
 = (M.fromList (
    [("add_decl", BratNode (Prim "add") [] [("thunk",
        VFun Braty B0 ([("a", Right TInt), ("b", Right TInt)] :-> [("c", Right TInt)]))])
    ,("kcr-cty", BratNode Hypo [("a", star_t), ("b", star_t), ("c", star_t)] [])
    ,("kcr-add", BratNode Hypo [("thunk", star_t)] [])
    ] ++ ints 3)
   ,[(Ex "int_1" 0, Right star_t, In "kcr-cty" 0)
    ,(Ex "int_2" 0, Right star_t, In "kcr-cty" 1)
    ,(Ex "int_3" 0, Right star_t, In "kcr-cty" 2)
    ]
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
  assertNoDifference msg act exp = let
      sub = \a b -> if a <= b then Nothing else Just (a - b)
      (mAct, mExp) = (M.differenceWith sub act exp, M.differenceWith sub exp act)
      sAct = intercalate "\n" (map show $ M.toList mAct)
      sExp = intercalate "\n" (map show $ M.toList mExp)
    in case (mAct, mExp) of
      (mAct, mExp)
        | M.null mAct, M.null mExp -> pure ()
        | M.null mAct -> assertFailure $ msg ++ " expected but not found: " ++ sExp
        | M.null mExp -> assertFailure $ msg ++ " found but not expected: " ++ sAct
        | otherwise -> assertFailure $ unlines [msg ++ " expected: " ++ sExp
                                             ," but found: " ++ sAct
                                             ]

runProg :: String -> String -> Graph -> Assertion
runProg name contents expected = do
  runExceptT (loadFiles ("" :| []) name contents) >>= \case
    Right (_, _, _, named_gs) -> let gs = map snd named_gs in
      -- merge graphs from all functions
      (fold gs) =? expected
    Left err -> assertFailure (show err)
