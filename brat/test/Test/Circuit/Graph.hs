module Test.Circuit.Graph (graphTests) where

-- Module for checking that the graph generated by type checking is what we expect
import Brat.Checker
import Brat.Checker.Monad
import Brat.Error
import Brat.FC
import Brat.Graph
import Brat.Load
import Brat.Syntax.Core (Term(..))
import Brat.Naming (Name, root)
import Brat.Checker
import Brat.Checker.Helpers
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Hasochism
import Test.Circuit.Common
import Test.Checking (runEmpty)

import qualified Control.Exception as CE (assert)
import Control.Monad.Except
import Data.Bifunctor
import Data.Tuple.HT
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure
import qualified Data.Map as M
import Data.List (delete)

fst3 (a,_,_) = a

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
  ,"addN(inp :: Int) -> (out :: Int)"
  ,"addN(n) = add(n, N)"
  ]

addN2 = unlines
  ["ext \"N\" N :: (value :: Int)"
  ,"ext \"add\" add :: {a :: Int, b :: Int -> c :: Int}"
  ,""
  ,"addN(inp :: Int) -> (out :: Int)"
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

mkTensor :: Checking (Name, Name, Name, [(Src, BinderType Brat)])
mkTensor = do
  (fooNode, _, foos,  _) <- next "foo" Source (S0,Some (Zy :* S0)) R0 (RPr ("out1", TNat) (RPr ("out2", TFloat) R0))
  (barNode, _, [bar], _) <- next "bar" Source (S0,Some (Zy :* S0)) R0 (RPr ("out1", TInt) R0)
  (quxNode, _, [qux], _) <- next "qux" Source (S0,Some (Zy :* S0)) R0 (RPr ("res", TText) R0)
  let outs = tensor foos [bar, qux]
  pure (fooNode, barNode, quxNode, outs)

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
                               ,graphTest "addNmain" addNmain addNmainGraph
                               ,graphTest "ext"  ext  extGraph
                               ,graphTest "empty" "" emptyGraph
                               ,graphTest "comment" comment emptyGraph
                               ]
