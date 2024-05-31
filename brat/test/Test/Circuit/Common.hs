{-# LANGUAGE OverloadedStrings #-}

module Test.Circuit.Common where

import Control.Arrow ((&&&))
import Control.Monad.Except (runExceptT)
import qualified Data.Map as M
import Data.Bifunctor (bimap)
import Data.Foldable (fold)
import Data.Functor ((<&>))
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..), toList)
import Data.String (IsString(..))
import Data.Text (pack)
import Data.Tuple.HT
import Data.Type.Equality ((:~:)(..))
import Test.Tasty (TestTree)
import Test.Tasty.HUnit
import Test.Tasty.Silver.Advanced (goldenTest1, GDiff(..), GShow(ShowText))

import Brat.Checker.Helpers (valueToBinder)
import Brat.Constructors (pattern CQubit)
import Brat.Eval (EvMode, kindType)
import Brat.Graph
import Brat.Load (loadFiles)
import Brat.Naming
import Brat.Syntax.Core
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName (plain)
import Bwd
import Hasochism

instance IsString Name where
  fromString s = MkName [(s, 0)]

kernel cty = VFun Kerny cty

singleClauseMatching :: forall m
                      . Show (BinderType m)
                      => Modey m
                      -> ([(String, Val Z)], [(String, Val Z)])
                      -> ([(String, Val Z)], [(String, Val Z)])
                      -> [(Name, Node)]
singleClauseMatching my (ins, outs) (matchedIns, matchedOuts) =
  [("box_branch_matched", BratNode (Box M.empty "matched_src" "matched_tgt") [] [("thunk", VFun my matchedKty)])
  ,("matched_src", node Source [] matchedIns)
  ,("matched_tgt", node Target matchedOuts [])

  ,("box_branch_didnt_match", BratNode (Box M.empty "didnt_match_src" "didnt_match_tgt") [] [("thunk", VFun my kty)])
  ,("didnt_match_src", node Source [] ins)
  ,("didnt_match_tgt", node Target outs [])

  ,("funclauses", node (FunClauses ((TestMatchData my
                                     (MatchSequence
                                       (bimap dummy (valueToBinder my) <$> ins)
                                       []
                                       (bimap dummy (valueToBinder my) <$> matchedIns))
                                   , "box_branch_matched") :| [])) [] [("value", VFun my (makeCTy ins outs))])
  ]
 where
  node = case my of
    Braty -> BratNode
    Kerny -> KernelNode

  matchedKty = makeCTy matchedIns matchedOuts
  kty = makeCTy ins outs

  makeCTy :: [(String, Val Z)] -> [(String, Val Z)] -> CTy m Z
  makeCTy ins outs = aux ins :->> aux outs

  aux :: [(String, Val Z)] -> Ro m Z Z
  aux [] = R0
  aux (x:xs) = RPr x (aux xs)

  dummy = NamedPort (Ex (MkName []) 0)

idGraph :: Graph
idGraph = (M.fromList $
           [("main_box", BratNode (Box M.empty "src" "tgt") [] [("thunk", kty)])
           ,("main", BratNode Id [("a1", kty)] [("a1", kty)])
           ,("src", KernelNode Source [] [("a", TQ)])
           ,("tgt", KernelNode Target [("b", TQ)] [])
           ,("qubit0", BratNode (Constructor CQubit) [] [("value", TUnit)])
           ,("qubit1", BratNode (Constructor CQubit) [] [("value", TUnit)])
           ]
          ,[((Ex "src" 0), TQ, (In "tgt" 0))
           ,((Ex "main_box" 0), kty, (In "main" 0))
           -- kind check node which doesn't make it into the graph above
           ,(Ex "qubit0" 0, TUnit, In "__kc0" 0)
           ,(Ex "qubit1" 0, TUnit, In "__kc1" 0)
           ]
          )
 where
  kty = kernel ((RPr ("a", TQ) R0) :->> (RPr ("b", TQ) R0))
  kty' = kernel ((RPr ("q", TQ) R0) :->> (RPr ("b", TQ) R0))

swapGraph :: Graph
swapGraph = (M.fromList $
             [("main_box", BratNode (Box M.empty "src" "tgt") [] [("thunk", kty)])
             ,("main", BratNode Id [("a1", kty)] [("a1", kty)])
             ,("src", KernelNode Source [] [("a", TQ), ("b", TQ)])
             ,("tgt", KernelNode Target [("b", TQ), ("a", TQ)] [])
             ,("qubit0", BratNode (Constructor CQubit) [] [("value", TUnit)])
             ,("qubit1", BratNode (Constructor CQubit) [] [("value", TUnit)])
             ,("qubit2", BratNode (Constructor CQubit) [] [("value", TUnit)])
             ,("qubit3", BratNode (Constructor CQubit) [] [("value", TUnit)])
             ]
            ,[((Ex "src" 0), TQ, (In "tgt" 1))
             ,((Ex "src" 1), TQ, (In "tgt" 0))
             ,((Ex "main_box" 0), kty, (In "main" 0))
             -- kind check node which doesn't make it into the graph above
             ,(Ex "qubit0" 0, TUnit, In "__kc0" 0)
             ,(Ex "qubit1" 0, TUnit, In "__kc0" 1)
             ,(Ex "qubit2" 0, TUnit, In "__kc1" 0)
             ,(Ex "qubit3" 0, TUnit, In "__kc1" 1)
             ]
            )
 where
  kty = kernel
        ((RPr ("a", TQ) (RPr ("b", TQ) R0)) :->> (RPr ("b", TQ) (RPr ("a", TQ) R0)))

xGraph :: Graph
xGraph = (M.fromList $
          [("tket.X", BratNode (Prim ("tket", "X")) [] [("a1", xTy)])
          ,("X", KernelNode (Splice (Ex "tket.X" 0)) [("xa", TQ)] [("xb", TQ)])
          ,("main_box", BratNode (Box M.empty "src" "tgt") [] [("thunk", mainTy)])
          ,("main", BratNode Id [("a1", mainTy)] [("a1", mainTy)])
          ,("src", KernelNode Source [] [("a", TQ)])
          ,("tgt", KernelNode Target [("b", TQ)] [])
          ,("qubit0", BratNode (Constructor CQubit) [] [("value", TUnit)])
          ,("qubit1", BratNode (Constructor CQubit) [] [("value", TUnit)])
          ,("qubit2", BratNode (Constructor CQubit) [] [("value", TUnit)])
          ,("qubit3", BratNode (Constructor CQubit) [] [("value", TUnit)])
          ]
         ,[((Ex "src" 0), TQ, (In "X" 0))
          ,((Ex "X" 0), TQ, (In "tgt" 0))
          ,((Ex "main_box" 0), mainTy, (In "main" 0))
          -- kind check node which doesn't make it into the graph above
          ,(Ex "qubit0" 0, TUnit, In "__kc0" 0)
          ,(Ex "qubit1" 0, TUnit, In "__kc1" 0)
          ,(Ex "qubit2" 0, TUnit, In "__kc2" 0)
          ,(Ex "qubit3" 0, TUnit, In "__kc3" 0)
          ]
         )
 where
  xTy = kernel ((RPr ("xa", TQ) R0) :->> (RPr ("xb", TQ) R0))
  mainTy = kernel ((RPr ("a", TQ) R0) :->> (RPr ("b", TQ) R0))

-- TODO:
rxGraph :: Graph
rxGraph = (M.fromList
           [("id", BratNode (Prim ("", "Rx"))
            [("th", TFloat)]
            [("kernel", kernel ((RPr ("a", TQ) R0) :->> (RPr ("b", TQ) R0)))])
           ,("angle", BratNode (Const (Float 30.0)) [("th", TFloat)] [])
           --,KernelNode (Splice "") testProcess
           ,("main", BratNode (Box M.empty "src" "tgt") [] [("thunk", kernel ((RPr ("a", TQ) R0) :->> (RPr ("b", TQ) R0)))])
           ,("src", KernelNode Source [] [("a", TQ)])
           ,("tgt", KernelNode Target [("b", TQ)] [])
           ,("qubit", BratNode (Constructor CQubit) [] [("value", TUnit)])
           ]
          ,[]
          )

int = TInt

twoGraph :: Graph
twoGraph = (M.fromList (
            [("add", BratNode (Prim ("", "add")) [] [("thunk", add_ty)])
            ,("add_eval", BratNode (Eval (Ex "add" 0)) [("a", int), ("b", int)] [("c", int)])
            ,("1a", BratNode (Const (Num 1)) [] [("value", int)])
            ,("1b", BratNode (Const (Num 1)) [] [("value", int)])
            ,("one", BratNode Id [("n", int)] [("n", int)])
            ,("two", BratNode Id [("a1", int)] [("a1", int)])
            ] ++ ints 5)
           ,[((Ex "1a" 0), int, (In "one" 0))
            ,((Ex "1b" 0), int, (In "add_eval" 0))
            ,((Ex "one" 0), int, (In "add_eval" 1))
            ,((Ex "add_eval" 0), int, (In "two" 0))
            --,(Ex "kcr-cty" 0, star_t, In "kcr-add" 0)
                -- no node exists to actually compute the function type. kcr-cty merely verifies
                -- that it is a well-formed type (by kindChecking its components, not putting them together)
            ,(Ex "int_1" 0, star_t, In "kcr-cty" 0)
            ,(Ex "int_2" 0, star_t, In "kcr-cty" 1)
            ,(Ex "int_3" 0, star_t, In "kcr-cty" 2)
            ,(Ex "int_4" 0, star_t, In "kcr-one" 0)
            ,(Ex "int_5" 0, star_t, In "kcr-two" 0)
            ]
           )
  where
    add_ty = VFun Braty $ (RPr ("a", int) (RPr ("b", int) R0)) :->> (RPr ("c", int) R0)

oneGraph :: Graph
oneGraph = (M.fromList (
            [("1", BratNode (Const (Num 1)) [] [("value", int)])
            ,("one", BratNode Id [("n", int)] [("n", int)])
            ] ++ ints 1)
           ,[((Ex "1" 0), int, (In "one" 0))
            ,((Ex "int" 0), star_t, (In "kcr" 0))]
           )

star_t = kindType $ Star []
ints :: Int -> [(Name, Node)]
ints n = [int_node (fromString $ "int_" ++ show x) | x <- [1..n]]
int_node :: Name -> (Name, Node)
int_node n = (n, BratNode (Constructor $ plain "Int") [] [("value", star_t)])

addNGraph :: String -> Graph
addNGraph port_name
  = (M.fromList (
     [("add", BratNode (Prim ("", "add")) [] [(port_name, add_ty)])
     ,("add_eval", BratNode (Eval (Ex "addN_src" 1)) [("a", int), ("b", int)] [("c", int)])
     ,("N", BratNode (Prim ("", "N")) [] [("value", int)])
     ,("addN", BratNode Id [("thunk", addN_ty)] [("thunk", addN_ty)])
     -- and one for the single clause
     ] ++ ints 6 ++ singleClauseMatching Braty ([("inp", TInt)], [("out", TInt)]) ([("n", TInt)], [("out", TInt)])
     )
    ,[(Ex "N" 0, int, In "addN_box" 1)
     ,(Ex "addN_box" 0, addN_ty, In "addN" 0)
     ,(Ex "addN_src" 0, int, In "add_eval" 0) -- argument
     ,(Ex "add_eval" 0, int, In "addN_tgt" 0)
     ,(Ex "int_1" 0, star_t, In "kcr-n" 0)
     ,(Ex "int_2" 0, star_t, In "kcr-add-ty" 0)
     ,(Ex "int_3" 0, star_t, In "kcr-add-ty" 1)
     ,(Ex "int_4" 0, star_t, In "kcr-add-ty" 2)
     ,(Ex "int_5" 0, star_t, In "kcr-addN-ty" 0)
     ,(Ex "int_6" 0, star_t, In "kcr-addN-ty" 1)
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
     ] ++ [int_node "xtra_int"]
     )
    ,ws ++ [
      (Ex "1" 0, int, In "addN_eval" 0)
     ,(Ex "addN_eval" 0, int, In "main" 0)
     ,(Ex "xtra_int" 0, star_t, In "kcr-main" 0)
     ]
    )
 where
  addN_ty = VFun Braty $ (RPr ("inp", TInt) R0) :->> (RPr ("out", TInt) R0)

extGraph :: Graph
extGraph
 = (M.fromList (
    ("add_decl", BratNode (Prim ("", "add")) [] [("thunk",
        VFun Braty ((RPr ("a", TInt) (RPr ("b", TInt) R0)) :->> (RPr ("c", TInt) R0)))])
    :ints 3)
   ,[(Ex "int_1" 0, star_t, In "kcr-cty" 0)
    ,(Ex "int_2" 0, star_t, In "kcr-cty" 1)
    ,(Ex "int_3" 0, star_t, In "kcr-cty" 2)
    ]
   )

graphDiff :: Graph -> Graph -> GDiff
graphDiff act exp = case act =? exp of
  (Nothing, _) -> Equal
  (msg, (act, exp)) -> DiffText msg (pack act) (pack exp)

-- Test the "close-enough" "equality" of two graphs
(=?) :: Graph -- Actual
     -> Graph -- Expected
     -> (Maybe String, (String, String))
(ns_act, ws_act) =? (ns_exp, ws_exp) = case (nodeEq, wireEq) of
  ((Nothing, _), _) -> wireEq
  _ -> nodeEq
 where
  wireEq :: (Maybe String, (String, String))
  wireEq = difference "Wires" (wireSet ws_act) (wireSet ws_exp)

  wireSet :: [Wire] -> M.Map String Int
  wireSet ws = foldr (M.alter inc) M.empty (wireKey <$> ws)

  wireKey :: Wire -> String
  wireKey (Ex _ p, ty, In _ p') = unwords [show p, "--", show ty, "->", show p']

  nodeEq :: (Maybe String, (String, String))
  nodeEq = difference "Nodes" (nodeSet ns_act) (nodeSet ns_exp)

  inc :: Maybe Int -> Maybe Int
  inc = Just . maybe 1 (1+)

  nodeTypeKey :: Modey m -> NodeType m -> String
  nodeTypeKey Braty = \case
    Prim (ext,op) -> "prim_" ++ (if ext /= "" then ext ++ "." else "") ++ op
    Const x    -> "const_" ++ show x
    Eval _     -> "eval"
    (Box _ _ _) -> "box"
    Source     -> "source"
    Target     -> "target"
    Id         -> "id"
    FunClauses cs -> "funclauses_" ++ show (length (toList cs))
    Hypo       -> "hypo"
    Constructor c -> "ctor_" ++ show c
    Selector c -> "selector_" ++ show c
    ArithNode op -> "arith_" ++ show op
  nodeTypeKey Kerny = ('k':) . \case
    Const x    -> "const_" ++ show x
    Splice _   -> "splice"
    Source     -> "source"
    Target     -> "target"
    Id         -> "id"
    FunClauses cs -> "funclauses_" ++ show (length (toList cs))
    Hypo       -> "hypo"
    Constructor c -> "ctor_" ++ show c
    Selector c -> "selector_" ++ show c

  nodeKey :: Node -> String
  nodeKey (BratNode thing ins outs)
    = nodeTypeKey Braty thing ++ (unlines [show ins, show outs])
  nodeKey (KernelNode thing ins outs)
    = nodeTypeKey Kerny thing ++ (unlines [show ins, show outs])

  nodeSet :: M.Map k Node -> M.Map String Int
  nodeSet ns = foldr (M.alter inc) M.empty (nodeKey <$> (snd <$> M.toList ns))

  -- `M.difference a b` finds things that are in `a` but not in `b`
  -- The first thing in the tuple is `Nothing` if they're equal
  difference :: String -> M.Map String Int -> M.Map String Int -> (Maybe String, (String, String)) -- Actual vs Expected
  difference msg act exp = let
      sub = \a b -> if a <= b then Nothing else Just (a - b)
      (mAct, mExp) = (M.differenceWith sub act exp, M.differenceWith sub exp act)
      sAct = intercalate "\n" (map show $ M.toList mAct)
      sExp = intercalate "\n" (map show $ M.toList mExp)
    in (, (sAct, sExp)) $ case (mAct, mExp) of
      (mAct, mExp)
        | M.null mAct, M.null mExp -> Nothing
        | M.null mAct -> Just (msg ++ " expected but not found: " ++ sExp)
        | M.null mExp -> Just (msg ++ " found but not expected: " ++ sAct)
        | otherwise -> Just $ unlines [msg ++ " expected: " ++ sExp
                                      ," but found: " ++ sAct
                                      ]

graphTest :: String -> String -> Graph -> TestTree
graphTest name contents expected = goldenTest1 name (pure $ Just expected) actual graphDiff (ShowText . pack . show) update
 where
  actual :: IO Graph
  actual = runExceptT (loadFiles root ("" :| []) name contents) >>= \case
    -- merge graphs from all functions
    Right (_, _, _, _, g) -> pure g
    Left err -> assertFailure (show err)

  update _ = putStrLn "Can't update golden file"
