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

import Brat.Eval (kindType)
import Brat.Graph
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

kernel cty = VFun Kerny cty

idGraph :: Graph
idGraph = (M.fromList
           [("main_box", BratNode ("src" :>>: "tgt") [] [("thunk", kty)])
           ,("main", BratNode Id [("a1", kty)] [("a1", kty)])
           ,("src", KernelNode Source [] [("a", VQ)])
           ,("tgt", KernelNode Target [("b", VQ)] [])
           ]
          ,[((Ex "src" 0), Left (VQ), (In "tgt" 0))
           ,((Ex "main_box" 0), Right kty, (In "main" 0))
           ]
          )
 where
  kty = kernel ((RPr ("a", VQ) R0) :->> (RPr ("b", VQ) R0))

swapGraph :: Graph
swapGraph = (M.fromList
             [("main_box", BratNode ("src" :>>: "tgt") [] [("thunk", kty)])
             ,("main", BratNode Id [("a1", kty)] [("a1", kty)])
             ,("src", KernelNode Source [] [("a", VQ), ("b", VQ)])
             ,("tgt", KernelNode Target [("b", VQ), ("a", VQ)] [])
             ]
            ,[((Ex "src" 0), Left (VQ), (In "tgt" 1))
             ,((Ex "src" 1), Left (VQ), (In "tgt" 0))
             ,((Ex "main_box" 0), Right kty, (In "main" 0))
             ]
            )
 where
  kty = kernel
        ((RPr ("a", VQ) (RPr ("b", VQ) R0)) :->> (RPr ("b", VQ) (RPr ("a", VQ) R0)))

xGraph :: Graph
xGraph = (M.fromList
          [("tket.X", BratNode (Prim "tket.X") [] [("a1", xTy)])
          ,("X", KernelNode (Eval (Ex "tket.X" 0)) [("xa", VQ)] [("xb", VQ)])
          ,("main_box", BratNode ("src" :>>: "tgt") [] [("thunk", mainTy)])
          ,("main", BratNode Id [("a1", mainTy)] [("a1", mainTy)])
          ,("src", KernelNode Source [] [("a", VQ)])
          ,("tgt", KernelNode Target [("b", VQ)] [])
          ]
         ,[((Ex "src" 0), Left (VQ), (In "X" 0))
          ,((Ex "X" 0), Left (VQ), (In "tgt" 0))
          ,((Ex "main_box" 0), Right mainTy, (In "main" 0))
          ]
         )
 where
  xTy = kernel ((RPr ("xa", VQ) R0) :->> (RPr ("xb", VQ) R0))
  mainTy = kernel ((RPr ("a", VQ) R0) :->> (RPr ("b", VQ) R0))

-- TODO:
rxGraph :: Graph
rxGraph = (M.fromList
           [("id", BratNode (Prim "Rx")
            [("th", TFloat)]
            [("kernel", kernel ((RPr ("a", VQ) R0) :->> (RPr ("b", VQ) R0)))])
           ,("angle", BratNode (Const (Float 30.0)) [("th", TFloat)] [])
           --,KernelNode (Eval "") testProcess
           ,("main", BratNode ("src" :>>: "tgt") [] [("thunk", kernel ((RPr ("a", VQ) R0) :->> (RPr ("b", VQ) R0)))])
           ,("src", KernelNode Source [] [("a", VQ)])
           ,("tgt", KernelNode Target [("b", VQ)] [])
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
    add_ty = VFun Braty $ (RPr ("a", int) (RPr ("b", int) R0)) :->> (RPr ("c", int) R0)

oneGraph :: Graph
oneGraph = (M.fromList (
            [("1", BratNode (Const (Num 1)) [] [("value", int)])
            ,("one", BratNode Id [("n", int)] [("n", int)])
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
     -- one box for the function
     ,("addN_box", BratNode ("addN_src" :>>: "addN_tgt") [(port_name, add_ty), ("value", int)] [("thunk", addN_ty)])
     ,("addN_src", BratNode Source [] [("inp", int), (port_name, add_ty), ("value", int)])
     ,("addN_tgt", BratNode Target [("out", int)] [])
     ,("addN", BratNode Id [("thunk", addN_ty)] [("thunk", addN_ty)])
     -- and one for the single clause
     ,("addN1_box", BratNode ("addN1_src" :>>: "addN1_tgt") [(port_name, add_ty), ("value", int)] [("thunk", addN_ty)])
     ,("addN1_src", BratNode Source [] [("inp", int), (port_name, add_ty), ("value", int)])
     ,("addN1_tgt", BratNode Target [("out", int)] [])
     ] ++ ints 6)
    ,[(Ex "N" 0, Right int, In "addN_box" 1)
     ,(Ex "add" 0, Right add_ty, In "addN_box" 0)
     ,(Ex "addN_box" 0, Right addN_ty, In "addN" 0)
     ,((Ex "addN_src" 0), Right int, (In "add_eval" 0)) -- argument
     ,((Ex "addN_src" 1), Right add_ty, In "addN1_box" 0) -- from (Source of) outer func to clause
     ,((Ex "addN_src" 2), Right int, (In "add_eval" 1)) -- captured
     ,((Ex "addN_src" 2), Right int, (In "addN1_box" 1))  -- from (Source of) outer func to clause
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
  add_ty = VFun Braty $ (RPr ("a", int) (RPr ("b", int) R0)) :->> (RPr ("c", int) R0)
  addN_ty = VFun Braty $ (RPr ("inp", int) R0) :->> (RPr ("out", int) R0)

addNmainGraph :: Graph
addNmainGraph =
  let (ns, ws) = addNGraph "thunk"
  in (M.fromList (
     (M.toList ns) ++
     [("addN_eval", BratNode (Eval (Ex "addN" 0)) [("inp", int)] [("out", int)])
     ,("1", BratNode (Const (Num 1)) [] [("value", int)])
     ,("main", BratNode Id [("a1", int)] [("a1", int)])
     ] ++ [int_node "xtra_int"])
    ,ws ++ [
      (Ex "1" 0, Right int, In "addN_eval" 0)
     ,(Ex "addN_eval" 0, Right int, In "main" 0)
     ,(Ex "xtra_int" 0, Right star_t, In "kcr-main" 0)
     ]
    )
 where
  addN_ty = VFun Braty $ (RPr ("inp", TInt) R0) :->> (RPr ("out", TInt) R0)

extGraph :: Graph
extGraph
 = (M.fromList (
    ("add_decl", BratNode (Prim "add") [] [("thunk",
        VFun Braty ((RPr ("a", TInt) (RPr ("b", TInt) R0)) :->> (RPr ("c", TInt) R0)))])
    :ints 3)
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

graphTest name file graph = testCase name (runProg name file graph)
