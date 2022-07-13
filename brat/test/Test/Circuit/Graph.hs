module Test.Circuit.Graph (graphTests) where

-- Module for checking that the graph generated by type checking is what we expect
import Brat.Error
import Brat.Graph
import Brat.Load
import Brat.Syntax.Core (Term(..), VType)
import Brat.Naming (Name)
import Test.Circuit.Common
import Brat.Checker
import Brat.Checker.Helpers (sigToRow)
import Brat.Syntax.Common
import Brat.FC

import qualified Control.Exception as CE (assert)
import Control.Monad.Except
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure
import qualified Data.Map as M
import Data.List (delete)

graphTest name file graph = testCase name (runProg name file graph)

idFile = unlines
  ["main :: { a :: Qubit -o b :: Qubit }"
  ,"main = { q -> q }"
  ]

swapFile = unlines
  ["main :: { a :: Qubit, b :: Qubit -o b :: Qubit, a :: Qubit}"
  ,"main = { q0, q1 -> q1, q0 }"
  ]

xFile = unlines
  ["ext \"tket.X\" X :: { xa :: Qubit -o xb :: Qubit }"
  ,""
  ,"main :: { a :: Qubit -o b :: Qubit }"
  ,"main = { q -> X(q) }"
  ]

rxFile = unlines
  ["ext \"Rx\" Rx :: (th :: Float) -> { rxa :: Qubit -o rxb :: Qubit }"
  ,""
  ,"nums :: (x :: Int), (y :: Int), (z :: Int)"
  ,"nums = 1, 2 ,3"
  ,""
  ,"xish :: { rxa :: Qubit -o rxb :: Qubit }"
  ,"xish = Rx(30.0)"
  ,""
  ,"main :: { a :: Qubit -o b :: Qubit }"
  ,"main = { q -> xish(q) }"
  ]

two = unlines
  ["ext \"add\" add :: (a :: Int), (b :: Int) -> (c :: Int)"
  ,""
  ,"one :: (n :: Int)"
  ,"one = 1"
  ,""
  ,"two :: Int"
  ,"two = add(1, one)"
  ]

one = unlines
  ["one :: (n :: Int)"
  ,"one = 1"
  ]

addN = unlines
  ["ext \"N\" N :: (value :: Int)"
  ,"ext \"add\" add :: (a :: Int), (b :: Int) -> (c :: Int)"
  ,""
  ,"addN :: (in :: Int) -> (out :: Int)"
  ,"addN(n) = add(n, N)"
  ]

addN2 = unlines
  ["ext \"N\" N :: (value :: Int)"
  ,"ext \"add\" add :: (a :: Int), (b :: Int) -> (c :: Int)"
  ,""
  ,"addN :: (in :: Int) -> (out :: Int)"
  ,"addN(n) = add(n, N)"
  ,""
  ,"main :: Int"
  ,"main = addN(1)"
  ]

ext =
  "ext \"add\" add :: (a :: Int), (b :: Int) -> (c :: Int)"

comment = unlines
  ["# This is a test"
  ,""
  ,"# This too"
  ,""
  ]

-- This allows comparing edges as sets, ignoring ordering
equalEdges :: [Wire] -> [Wire] -> Assertion
equalEdges actual expected = do
  actual <- key_by_src actual
  expected <- key_by_src expected
  actual @?= expected
 where
  dup_wires s _ _ = assertFailure $ "Multiple wires for same source: " ++ (show s)
  key_by_src :: [Wire] -> IO (M.Map Src Wire)
  key_by_src ws = do
    let ioVals = M.fromListWithKey dup_wires (map (\w@(src,_,_) -> (src, pure w)) ws)
    M.fromList <$> (sequence $ map (\(k,iov) -> (k,) <$> iov) $ M.assocs ioVals)

dummyFC = FC (Pos 0 0) (Pos 0 0)

mkTensor :: Checking (Name, Name, Name, [(Src, VType)])
mkTensor = do
  foo <- next "foo" Source [] [("out1", SimpleTy Natural), ("out2", SimpleTy FloatTy)]
  bar <- next "bar" Source [] [("out1", SimpleTy IntTy)]
  qux <- next "qux" Source [] [("res", SimpleTy TextType)]
  outs <- tensor [((foo, "out1"), SimpleTy Natural),((foo, "out2"), SimpleTy FloatTy)] [((bar, "out1"), SimpleTy IntTy), ((qux, "res"), SimpleTy TextType)]
  pure (foo, bar, qux, outs)

isCombo :: Thing -> Bool
isCombo (Combo _) = True
isCombo _ = False

tensorOutputsTests :: TestTree
tensorOutputsTests = testCase "tensorOutputs" $ case run (emptyEnv, [], dummyFC) mkTensor of
  Left err -> assertFailure (show err)
  Right ((foo, bar, qux, outs), (holes, (nodes, edges))) -> do
    (M.size nodes) @=? 4 -- three input nodes and one combo
    let combo_nodes = (M.assocs nodes) >>= (\(name, node) -> if (isCombo $ nodeThing node) then [name] else [])
    (length combo_nodes) @?= 1
    let combo_node = head combo_nodes
    (length outs) @?= 4 -- four wires/ports
    mapM (@?= combo_node) (map (fst.fst) outs)
    let actualPorts = M.fromList $ map (\((n,p),ty) -> (p,ty)) outs
    let expectedPorts = M.fromList [("out1", SimpleTy Natural), ("out2", SimpleTy FloatTy), ("out3", SimpleTy IntTy), ("res", SimpleTy TextType)]
    actualPorts @?= expectedPorts
    edges `equalEdges` [
        ((foo,"out1"), Right (SimpleTy Natural), (combo_node, "out1")),
        ((foo,"out2"), Right (SimpleTy FloatTy), (combo_node, "out2")),
        ((bar,"out1"), Right (SimpleTy IntTy), (combo_node, "out3")),
        ((qux,"res"), Right (SimpleTy TextType), (combo_node, "res"))]

-- This is just because we have to pass some term into checkOutputs in case it needs to produce an error message.
-- But our case should never have to produce an error message, so assert false.
dummyTerm = CE.assert False (WC dummyFC $ Bound 0)

subtractThunksTest :: TestTree
subtractThunksTest = testCase "subtractThunks" $ case run (emptyEnv, [], dummyFC) mkThunks of
  Left err -> assertFailure (show err)
  Right ((inNode, outNode, unders), (_holes, (nodes, edges))) -> do
      (length unders) @?= 0
      (M.size nodes) @=? 4 -- input, output, 2*combo
      let combo_nodes = filter (isCombo.nodeThing.snd) (M.assocs nodes)
      (length combo_nodes) @?= 2
      -- one combo node has an edge to the output
      let [e@((combo1,_),_,_)] = (filter (\(_,_,(tgt,_)) -> tgt == outNode) edges)
      let [combo2] = delete combo1 (map fst combo_nodes)
      edges `equalEdges` [
         ((inNode, "arg1"), Right aFn, (combo1, "in1"))
        ,((inNode, "arg2"), Right bFn, (combo2, "in1"))
        -- note there is some renaming of the ports of the passed function here, to suit the target (not source)
        ,((inNode, "arg3"), Right (C ([("z", SimpleTy TextType)] :-> [("z", SimpleTy TextType)])), (combo2, "in2"))
        ,((combo2, "fun"), let bc =[("y", SimpleTy FloatTy), ("z", SimpleTy TextType)] in Right (C (bc :-> bc)), (combo1, "in2"))
        ,((combo1, "fun"), Right combinedFn, (outNode, "combined"))
        ]
 where
   aFn = C ([("a", SimpleTy IntTy)] :-> [("a", SimpleTy IntTy)])
   bFn = C ([("b", SimpleTy FloatTy)] :-> [("b", SimpleTy FloatTy)])
   cFn = C ([("c", SimpleTy TextType)] :-> [("c", SimpleTy TextType)])
   combinedFn = let tupleTy = [("x", SimpleTy IntTy), ("y", SimpleTy FloatTy), ("z", SimpleTy TextType)]
     in C (tupleTy :-> tupleTy)
   mkThunks :: Checking (Name, Name, [(Tgt, VType)])
   mkThunks = do
    let args = [("arg1", aFn), ("arg2", bFn), ("arg3", cFn)]
    let combinedOut = [("combined", combinedFn)]
    inNode <- next "in" Source [] args
    outNode <- next "out" Target combinedOut []
    unders <- checkOutputs dummyTerm (sigToRow outNode combinedOut) (sigToRow inNode args)
    return (inNode, outNode, unders)


graphTests = testGroup "Graph" [graphTest "id" idFile idGraph
                               ,graphTest "swap" swapFile swapGraph
                               ,graphTest "X"  xFile  xGraph
                               ,expectFail $ graphTest "Rx" rxFile rxGraph
                               ,graphTest "two" two   twoGraph
                               ,graphTest "one" one   oneGraph
                               ,graphTest "addN" addN addNGraph
                               ,expectFail $ graphTest "addN2" addN2 addN2Graph
                               ,graphTest "ext"  ext  extGraph
                               ,graphTest "empty" "" emptyGraph
                               ,graphTest "comment" comment emptyGraph
                               ,tensorOutputsTests
                               ,subtractThunksTest
                               ]
