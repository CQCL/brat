{-# LANGUAGE ScopedTypeVariables #-}

module Test.Combine (combineTests) where

import Brat.Checker
import Brat.Checker.Combine
import Brat.FC
import Brat.Graph
import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Core

import Data.List.NonEmpty (NonEmpty(..), fromList)

import Test.Tasty
import Test.Tasty.HUnit

fc = FC (Pos 0 0) (Pos 0 0)
src = MkName []
int = SimpleTy IntTy
bool = SimpleTy Boolean

checkingIsEqual :: (Eq a, Show a)
         => Checking a -- Actual
         -> a          -- Expected
         -> Assertion
checkingIsEqual m exp =
  case run ([],[],fc) m of
    Right (x, _) -> x @?= exp
    Left err -> assertFailure (show err)


inertTest = testCase "Don't combine non-thunks" $
            checkingIsEqual (combinationsWithLeftovers input) expected
 where
  i = ((src, "id1"), SimpleTy IntTy)
  f = ((src, "id2"), C ([("x", int),("y",int)] :-> [("x", int),("y", int)]))

  input :: NonEmpty (Src, VType)
  input = (i :| [f])

  expected :: NonEmpty ((Src, VType), [(Src, VType)])
  expected = (i, [f]) :| []

testThunk = testCase "Thunk" $ checkingIsEqual (combinationsWithLeftovers input) expected
 where
  input :: NonEmpty (Src, VType)
  input = fromList
    [((src, "id1"), C ([("x", int)] :-> [("x", int)]))
    ,((src, "id2"), C ([("x", int),("y",int)] :-> [("x", int),("y", int)]))
    ,((src, "id3"), C ([("x", int),("y",int),("z",int)] :-> [("x", int),("y", int),("z",int)]))
    ]

  combo = MkName [(show (src, "id1") ++ "_" ++ show (src, "id2"), 0)]
  combo' = MkName [(show (combo, "fun") ++ "_" ++ show (src, "id3"),1)]

  expected :: NonEmpty ((Src, VType), [(Src, VType)])
  expected = fromList
             [(((src, "id1"), C ([("x", int)] :-> [("x", int)]))
              ,[((src, "id2"), C ([("x", int),("y",int)] :-> [("x", int),("y", int)]))
               ,((src, "id3"), C ([("x", int),("y",int),("z",int)] :-> [("x", int),("y", int),("z",int)]))
               ]
              )
             ,(((combo, "fun"),
                 C ([("x", int),("x1", int),("y",int)]
                    :->
                    [("x", int),("x1", int),("y", int)]))
              ,[((src, "id3")
                ,C ([("x", int),("y",int),("z",int)]
                    :->
                    [("x", int),("y", int),("z",int)]))
               ]
              )
             ,(((combo', "fun")
               ,C ([("x", int),("x1", int),("y",int),("x2", int),("y1",int),("z",int)]
                   :->
                   [("x", int),("x1", int),("y",int),("x2", int),("y1",int),("z",int)])
               )
              ,[]
              )
             ]

testKernel = testCase "Kernel" $ checkingIsEqual (combinationsWithLeftovers input) expected
 where
  q = Q Qubit

  comboSrc = (MkName [(show (src, "id3") ++ "_" ++ show (src, "id2"),0)], "fun")

  input :: NonEmpty (Src, VType)
  input = fromList
    [((src, "id3"), K (R [("x", q),("y",q),("z",q)]) (R [("x", q),("y", q),("z",q)]))
    ,((src, "id2"), K (R [("x", q),("y",q)]) (R [("x", q),("y", q)]))
    ,((src, "id1"), K (R [("x", q)]) (R [("x", q)]))
    ]

  expected :: NonEmpty ((Src, VType), [(Src, VType)])
  expected = fromList
             [(((src, "id3"), K (R [("x", q),("y",q),("z",q)]) (R [("x", q),("y", q),("z",q)]))
              ,[((src, "id2"), K (R [("x", q),("y",q)]) (R [("x", q),("y", q)]))
               ,((src, "id1"), K (R [("x", q)]) (R [("x", q)]))
               ]
              )

             ,((comboSrc
               ,K
                (R [("x",q),("y",q),("z",q),("x1",q),("y1",q)])
                (R [("x",q),("y",q),("z",q),("x1",q),("y1",q)]))
              ,[((src, "id1")
                , K
                  (R [("x", q)])
                  (R [("x", q)])
                )
               ]
              )
             ,(((MkName [(show comboSrc ++ "_" ++ show (src, "id1"), 1)], "fun")
               ,K
                (R [("x", q),("y", q),("z",q),("x1", q),("y1",q),("x2",q)])
                (R [("x", q),("y", q),("z",q),("x1", q),("y1",q),("x2",q)])
               )
              ,[]
              )
             ]

headTest = testCase "thunk.head" $ checkingIsEqual (combineHead input) (Just exp)
 where
  fc = FC (Pos 0 0) (Pos 0 0)
  src = MkName []
  input :: [(Src, VType)]
  input = [((src,"f"), C ([("i", int)] :-> [("o", int)])), ((src,"g"), C ([("i", bool)] :-> [("o", bool)]))]
  combo = MkName [(show (src, "f") ++ "_" ++ show (src, "g"), 0)]
  exp :: ((Src, VType), [(Src, VType)])
  exp = (((combo, "fun"), C ([("i", int), ("i1", bool)] :-> [("o", int), ("o1", bool)])), [])

headTest2 = testCase "thunk.head2" $ checkingIsEqual (combinationsWithLeftovers input) exp
 where
  fc = FC (Pos 0 0) (Pos 0 0)
  src = MkName []
  input :: NonEmpty (Src, VType)
  input = fromList [((src,"f"), C ([("i", int)] :-> [("o", int)])), ((src,"g"), C ([("i", bool)] :-> [("o", bool)]))]
  combo = MkName [(show (src, "f") ++ "_" ++ show (src, "g"), 0)]
  exp :: NonEmpty ((Src, VType), [(Src, VType)])
  exp = fromList
        [(((src,"f"), C ([("i", int)] :-> [("o", int)]))
         ,[((src,"g"), C ([("i", bool)] :-> [("o", bool)]))]
         )
        ,(((combo, "fun"), C ([("i", int), ("i1", bool)] :-> [("o", int), ("o1", bool)]))
         ,[]
         )
        ]

ctypeNames = testCase "sanity" $
  let cty :: CType
        = [("a", SimpleTy IntTy), ("a1", SimpleTy IntTy)] :-> [("a2", SimpleTy IntTy)]
      exp :: CType
        = [("a", SimpleTy IntTy)
          ,("a1", SimpleTy IntTy)
          ,("a2", SimpleTy IntTy)
          ,("a3", SimpleTy IntTy)
          ] :->
          [("a2", SimpleTy IntTy)
          ,("a3", SimpleTy IntTy)
          ]
  in (cty <> cty) @?= exp

combineTests :: TestTree
combineTests
  = testGroup "combine"
    [inertTest
    ,testThunk
    ,testKernel
    ,headTest
    ,headTest2
    ,ctypeNames
    ]
