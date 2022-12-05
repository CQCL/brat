module Test.Circuit.Graph (graphTests) where

-- Module for checking that the graph generated by type checking is what we expect
import Brat.Error
import Brat.Graph
import Brat.Load
import Brat.Syntax.Core (Term(..), VType)
import Brat.Naming (Name)
import Test.Circuit.Common
import Brat.Checker
import Brat.Checker.Helpers
import Brat.Syntax.Common
import Brat.FC
import Brat.UserName
import Test.Checking (runEmpty)

import qualified Control.Exception as CE (assert)
import Control.Monad.Except
import Data.Tuple.HT
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure
import qualified Data.Map as M
import Data.List (delete)

graphTest name file graph = testCase name (runProg name file graph)

idFile = unlines
  ["main :: { a :: Qubit -o b :: Qubit }"
  ,"main = { q => q }"
  ]

swapFile = unlines
  ["main :: { a :: Qubit, b :: Qubit -o b :: Qubit, a :: Qubit}"
  ,"main = { q0, q1 => q1, q0 }"
  ]

xFile = unlines
  ["ext \"tket.X\" X :: { xa :: Qubit -o xb :: Qubit }"
  ,""
  ,"main :: { a :: Qubit -o b :: Qubit }"
  ,"main = { q => X(q) }"
  ]

rxFile = unlines
  ["ext \"Rx\" Rx(th :: Float) -> { rxa :: Qubit -o rxb :: Qubit }"
  ,""
  ,"nums :: (x :: Int), (y :: Int), (z :: Int)"
  ,"nums = 1, 2 ,3"
  ,""
  ,"xish :: { rxa :: Qubit -o rxb :: Qubit }"
  ,"xish = Rx(30.0)"
  ,""
  ,"main :: { a :: Qubit -o b :: Qubit }"
  ,"main = { q => xish(q) }"
  ]

two = unlines
  ["ext \"add\" add(a :: Int, b :: Int) -> (c :: Int)"
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
  ,"ext \"add\" add(a :: Int, b :: Int) -> (c :: Int)"
  ,""
  ,"addN(in :: Int) -> (out :: Int)"
  ,"addN(n) = add(n, N)"
  ]

addN2 = unlines
  ["ext \"N\" N :: (value :: Int)"
  ,"ext \"add\" add :: {a :: Int, b :: Int -> c :: Int}"
  ,""
  ,"addN(in :: Int) -> (out :: Int)"
  ,"addN(n) = add(n, N)"
  ]

addNmain = addN ++ unlines
  [""
  ,"main :: Int"
  ,"main = addN(1)"
  ]

ext =
  "ext \"add\" add(a :: Int, b :: Int) -> (c :: Int)"

comment = unlines
  ["-- This is a test"
  ,""
  ,"-- This too"
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
  key_by_src :: [Wire] -> IO (M.Map OutPort Wire)
  key_by_src ws = do
    let ioVals = M.fromListWithKey dup_wires (map (\w@(src,_,_) -> (src, pure w)) ws)
    M.fromList <$> (sequence $ map (\(k,iov) -> (k,) <$> iov) $ M.assocs ioVals)

mkTensor :: Checking (Name, Name, Name, [(Src, VType)])
mkTensor = do
  (fooNode, _, foos) <- next "foo" Source [] [("out1", SimpleTy Natural), ("out2", SimpleTy FloatTy)]
  (barNode, _, [bar]) <- next "bar" Source [] [("out1", SimpleTy IntTy)]
  (quxNode, _, [qux]) <- next "qux" Source [] [("res", SimpleTy TextType)]
  outs <- tensor foos [bar, qux]
  pure (fooNode, barNode, quxNode, outs)

isCombo :: Thing -> Bool
isCombo (Combo _) = True
isCombo _ = False

tensorOutputsTests :: TestTree
tensorOutputsTests = testCase "tensorOutputs" $ case runEmpty mkTensor of
  Left err -> assertFailure (show err)
  Right ((foo, bar, qux, outs), (holes, (nodes, edges))) -> do
    (M.size nodes) @=? 4 -- three input nodes and one combo
    let combo_nodes = (M.assocs nodes) >>= (\(name, node) -> if (isCombo $ nodeThing node) then [name] else [])
    (length combo_nodes) @?= 1
    let combo_node = head combo_nodes
    (length outs) @?= 4 -- four wires/ports
    mapM (@?= combo_node) (map (\(NamedPort (Ex n _) _, _ty) -> n) outs)
    let actualPorts = M.fromList $ map (\(p,ty) -> (portName p,ty)) outs
    let expectedPorts = M.fromList [("out1", SimpleTy Natural), ("out2", SimpleTy FloatTy), ("out1", SimpleTy IntTy), ("res", SimpleTy TextType)]
    actualPorts @?= expectedPorts
    edges `equalEdges`
      [((Ex foo 0), Right (SimpleTy Natural), (In combo_node 0))
      ,((Ex foo 1), Right (SimpleTy FloatTy), (In combo_node 1))
      ,((Ex bar 0), Right (SimpleTy IntTy), (In combo_node 2))
      ,((Ex qux 0), Right (SimpleTy TextType), (In combo_node 3))]

-- This is just because we have to pass some term into checkOutputs in case it needs to produce an error message.
-- But our case should never have to produce an error message, so assert false.
dummyTerm = CE.assert False (dummyFC $ Var (PrefixName [] ""))

graphTests = testGroup "Graph" [graphTest "id" idFile idGraph
                               ,graphTest "swap" swapFile swapGraph
                               ,graphTest "X"  xFile  xGraph
                               ,expectFail $ graphTest "Rx" rxFile rxGraph
                               ,graphTest "two" two   twoGraph
                               ,graphTest "one" one   oneGraph
                               ,graphTest "addN" addN (addNGraph "thunk")
                               ,graphTest "addN2" addN2 (addNGraph "a1")
                               ,expectFail $ graphTest "addNmain" addNmain addNmainGraph
                               ,graphTest "ext"  ext  extGraph
                               ,graphTest "empty" "" emptyGraph
                               ,graphTest "comment" comment emptyGraph
                               ,tensorOutputsTests
                               ]
