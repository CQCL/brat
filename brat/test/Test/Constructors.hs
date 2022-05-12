{-# LANGUAGE OverloadedStrings #-}

module Test.Constructors (constructorTests) where

import Brat.Load
import Brat.Graph
import Brat.Syntax.Core
import Brat.Syntax.Common

import Test.Circuit.Common

import Control.Monad.Except
import Test.Tasty
import Test.Tasty.HUnit

listProg :: String
listProg =
  unlines
  ["xs :: List(Int)"
  ,"xs = [1,2,3]"
  ]

listGraph :: Graph' Term
listGraph =
  ([BratNode "xs" Id [("a1", List (SimpleTy IntTy))] [("a1", List (SimpleTy IntTy))]
   ,BratNode "mklist" (Constructor CList)
     [("e0", SimpleTy IntTy)
     ,("e1", SimpleTy IntTy)
     ,("e2", SimpleTy IntTy)
     ]
     [("value", List (SimpleTy IntTy))]
   ,BratNode "1" (Const (Num 1)) [] [("value", SimpleTy IntTy)]
   ,BratNode "2" (Const (Num 2)) [] [("value", SimpleTy IntTy)]
   ,BratNode "3" (Const (Num 3)) [] [("value", SimpleTy IntTy)]
   ]
  ,[(("1", "value"), Right (SimpleTy IntTy), ("mklist", "e0"))
   ,(("2", "value"), Right (SimpleTy IntTy), ("mklist", "e1"))
   ,(("3", "value"), Right (SimpleTy IntTy), ("mklist", "e2"))
   ,(("mklist", "value"), Right (List (SimpleTy (IntTy))), ("xs", "a1"))
   ]
  )

listTest = testCase "list" $ runProg "list" listProg listGraph

vecProg :: String
vecProg =
  unlines
  ["xs :: Vec(Int,3)"
  ,"xs = [0,1,2]"
  ]

vecGraph :: Graph' Term
vecGraph =
  ([BratNode "xs" Id
    [("a1", Vector (SimpleTy IntTy) (Simple (Num 3)))]
    [("a1", Vector (SimpleTy IntTy) (Simple (Num 3)))]
   ,BratNode "mkvec" (Constructor CVec)
     [("e0", SimpleTy IntTy)
     ,("e1", SimpleTy IntTy)
     ,("e2", SimpleTy IntTy)
     ]
     [("value", Vector (SimpleTy IntTy) (Simple (Num 3)))]
   ,BratNode "0" (Const (Num 0)) [] [("value", SimpleTy IntTy)]
   ,BratNode "1" (Const (Num 1)) [] [("value", SimpleTy IntTy)]
   ,BratNode "2" (Const (Num 2)) [] [("value", SimpleTy IntTy)]
   -- This is for the type of the vector
   ,BratNode "3" (Const (Num 3)) [] [("value", SimpleTy Natural)]
   ,BratNode "hypo" Hypo [("ty", SimpleTy Natural)] []
   ]
  ,[(("0", "value"), Right (SimpleTy IntTy), ("mkvec", "e0"))
   ,(("1", "value"), Right (SimpleTy IntTy), ("mkvec", "e1"))
   ,(("2", "value"), Right (SimpleTy IntTy), ("mkvec", "e2"))
   ,(("3", "value"), Right (SimpleTy Natural), ("hypo", "ty"))
   ,(("mkvec", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 3))), ("xs", "a1"))
   ]
  )

vecTest = testCase "vec" $ runProg "vec" vecProg vecGraph

pairProg :: String
pairProg =
  unlines
  ["xs :: Pair(Int, Bool)"
  ,"xs = [1,true]"
  ]

pairGraph :: Graph' Term
pairGraph =
  ([BratNode "xs" Id
     [("a1", Product (SimpleTy IntTy) (SimpleTy Boolean))]
     [("a1", Product (SimpleTy IntTy) (SimpleTy Boolean))]
   ,BratNode "mkpair" (Constructor CPair)
     [("first", SimpleTy IntTy)
     ,("second", SimpleTy Boolean)
     ]
     [("value", Product (SimpleTy IntTy) (SimpleTy Boolean))]
   ,BratNode "1" (Const (Num 1)) [] [("value", SimpleTy IntTy)]
   ,BratNode "true" (Const (Bool True)) [] [("value", SimpleTy Boolean)]
   ]
  ,[(("1", "value"),    Right (SimpleTy IntTy), ("mkpair", "first"))
   ,(("true", "value"), Right (SimpleTy Boolean), ("mkpair", "second"))
   ,(("mkpair", "value"), Right (Product (SimpleTy IntTy) (SimpleTy Boolean)), ("xs", "a1"))
   ]
  )

pairTest = testCase "pair" $ runProg "pair" pairProg pairGraph

consProg :: String
consProg =
  unlines
  ["two :: Vec(Int,2)"
  ,"two = [1,2]"
  ,""
  ,"three :: Vec(Int,3)"
  ,"three = cons(0,two)"
  ]

consGraph :: Graph' Term
consGraph =
  ([BratNode "three" Id
     [("a1", Vector (SimpleTy IntTy) (Simple (Num 3)))]
     [("a1", Vector (SimpleTy IntTy) (Simple (Num 3)))]
   ,BratNode "two" Id
     [("a1", Vector (SimpleTy IntTy) (Simple (Num 2)))]
     [("a1", Vector (SimpleTy IntTy) (Simple (Num 2)))]

   ,BratNode "vec.cons" (Constructor CCons)
     [("head", SimpleTy IntTy)
     ,("tail", Vector (SimpleTy IntTy) (Simple (Num 2)))
     ]
     [("value", Vector (SimpleTy IntTy) (Simple (Num 3)))]

   ,BratNode "mkvec" (Constructor CVec)
     [("e0", SimpleTy IntTy)
     ,("e1", SimpleTy IntTy)
     ]
     [("value", Vector (SimpleTy IntTy) (Simple (Num 2)))]

   ,BratNode "0" (Const (Num 0)) [] [("value", SimpleTy IntTy)]
   ,BratNode "1" (Const (Num 1)) [] [("value", SimpleTy IntTy)]
   ,BratNode "2" (Const (Num 2)) [] [("value", SimpleTy IntTy)]
   ,BratNode "2" (Const (Num 2)) [] [("value", SimpleTy Natural)]
   ,BratNode "3" (Const (Num 3)) [] [("value", SimpleTy Natural)]
   ,BratNode "hypo2" Hypo [("ty", SimpleTy Natural)] []
   ,BratNode "hypo3" Hypo [("ty", SimpleTy Natural)] []
   ]
  ,[(("0", "value"), Right (SimpleTy IntTy), ("vec.cons", "head"))
   ,(("1", "value"), Right (SimpleTy IntTy), ("mkvec", "e0"))
   ,(("2", "value"), Right (SimpleTy IntTy), ("mkvec", "e1"))
   ,(("2", "value"), Right (SimpleTy Natural), ("hypo2", "ty"))
   ,(("3", "value"), Right (SimpleTy Natural), ("hypo3", "ty"))
   ,(("mkvec", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), ("two", "a1"))
   ,(("vec.cons", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 3))), ("three", "a1"))
   ,(("two", "a1"), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), ("vec.cons", "tail"))
   ]
  )

consTest = testCase "cons" $ runProg "cons" consProg consGraph

numProg :: String
numProg =
  unlines
  ["n :: Nat"
  ,"n = succ(2)"
  ,""
  ,"m :: Int"
  ,"m = doub(-3)"
  ]

numGraph :: Graph' Term
numGraph =
  ([BratNode "n" Id
     [("a1", SimpleTy Natural)]
     [("a1", SimpleTy Natural)]
   ,BratNode "m" Id
     [("a1", SimpleTy IntTy)]
     [("a1", SimpleTy IntTy)]

   ,BratNode "succ" (Constructor CSucc)
     [("value", SimpleTy Natural)]
     [("value", SimpleTy Natural)]

   ,BratNode "doub" (Constructor CDoub)
     [("value", SimpleTy IntTy)]
     [("value", SimpleTy IntTy)]

   ,BratNode "2" (Const (Num 2)) [] [("value", SimpleTy Natural)]
   ,BratNode "-3" (Const (Num (-3))) [] [("value", SimpleTy IntTy)]
   ]
  ,[(("2", "value"), Right (SimpleTy Natural), ("succ", "value"))
   ,(("succ","value"), Right (SimpleTy Natural), ("n", "a1"))
   ,(("-3", "value"), Right (SimpleTy IntTy), ("doub", "value"))
   ,(("doub","value"), Right (SimpleTy IntTy), ("m", "a1"))
   ]
  )

numTest = testCase "num" $ runProg "num" numProg numGraph

kernelProg :: String
kernelProg =
  unlines
  ["id3 :: { Qubit, Qubit, Qubit -o Vec(Qubit,3) }"
  ,"id3 = { q0, q1, q2 -> cons(q0, [q1, q2]) }"
  ]

kernelGraph :: Graph' Term
kernelGraph =
  ([BratNode "id3" Id
     [("a1", ktype)]
     [("a1", ktype)]

   ,KernelNode "mkvec" (Constructor CVec)
     [("e0", Q Qubit), ("e1", Q Qubit)]
     [("value", Of (Q Qubit) (Simple (Num 2)))]

   ,KernelNode "vec.cons" (Constructor CCons)
     [("head", Q Qubit), ("tail", Of (Q Qubit) (Simple (Num 2)))]
     [("value", Of (Q Qubit) (Simple (Num 3)))]

   ,KernelNode "src" Source [] [("a1", Q Qubit), ("b1", Q Qubit), ("c1", Q Qubit)]
   ,KernelNode "tgt" Target [("a1", Of (Q Qubit) (Simple (Num 3)))] []

   ,BratNode "kbox" ("src" :>>: "tgt") [] [("fun", ktype)]

   ,BratNode "2" (Const (Num 2)) [] [("value", SimpleTy Natural)]
   ,BratNode "3" (Const (Num 3)) [] [("value", SimpleTy Natural)]
   ,BratNode "hypo2" Hypo [("ty", SimpleTy Natural)] []
   ,BratNode "hypo3" Hypo [("ty", SimpleTy Natural)] []
   ]
  ,[(("src", "a1"), Left (Q Qubit), ("vec.cons", "head"))
   ,(("src", "b1"), Left (Q Qubit), ("mkvec", "e0"))
   ,(("src", "c1"), Left (Q Qubit), ("mkvec", "e1"))
   ,(("kbox", "fun"), Right ktype, ("id3", "a1"))
   ,(("mkvec", "value"), Left (Of (Q Qubit) (Simple (Num 2))), ("vec.cons", "tail"))
   ,(("vec.cons", "value"), Left (Of (Q Qubit) (Simple (Num 3))), ("tgt", "a1"))
   ,(("2", "value"), Right (SimpleTy Natural), ("hypo2", "ty"))
   ,(("3", "value"), Right (SimpleTy Natural), ("hypo3", "ty"))
   ]
  )
 where
  ktype = K (R [("a1", Q Qubit), ("b1", Q Qubit), ("c1", Q Qubit)]) (R [("a1", Of (Q Qubit) (Simple (Num 3)))])

kernelTest = testCase "kernel" $ runProg "kernel" kernelProg kernelGraph

constructorTests = testGroup "Constructors" [listTest,vecTest,pairTest,consTest,numTest,kernelTest]
