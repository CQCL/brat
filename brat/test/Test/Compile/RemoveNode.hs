module Test.Compile.RemoveNode (removeNodeTests) where

import Brat.Compile.Simple
import Brat.Graph
import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Test.Circuit.Common

import qualified Data.Map as M
import Test.Tasty
import Test.Tasty.HUnit

-- Remove these after the Test.Util module is added
a = MkName [("a", 0)]
b = MkName [("b", 0)]
c = MkName [("c", 0)]
out = MkName [("out", 0)]

dummyNode = BratNode (Const (Num 3)) [] [("value", int)]
idNode = BratNode Id [("in", int)] [("out", int)]
outNode = BratNode Target [("sink", int)] []

testGraph =
        (M.fromList
          [(a, dummyNode)
          ,(b, idNode)
          ,(c, idNode)
          ,(out, outNode)
          ]
        ,[((Ex a 0), Right int, (In b 0))
         ,((Ex b 0), Right int, (In c 0))
         ,((Ex c 0), Right int, (In out 0))
         ]
        )

removeA = testCase "removeNode.a" $ do
  let exp = 
        (M.fromList
          [(b, idNode)
          ,(c, idNode)
          ,(out, outNode)
          ]
        ,[((Ex b 0), Right int, (In c 0))
         ,((Ex c 0), Right int, (In out 0))
         ]
        )
    in removeNode a testGraph =? exp

removeB = testCase "removeNode.b" $ do
  let exp = 
        (M.fromList
          [(a, dummyNode)
          ,(c, idNode)
          ,(out, outNode)
          ]
        ,[((Ex c 0), Right int, (In out 0))]
        )
    in removeNode b testGraph =? exp

removeNodeTests = testGroup "removeNode" [removeA, removeB]
