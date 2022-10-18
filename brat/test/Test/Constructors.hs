{-# LANGUAGE OverloadedStrings #-}

module Test.Constructors (constructorTests) where

import Brat.Load
import Brat.Graph
import Brat.Syntax.Core
import Brat.Syntax.Common

import Test.Circuit.Common

import Control.Monad.Except
import Data.Map (fromList)
import Test.Tasty
import Test.Tasty.HUnit

listProg :: String
listProg =
  unlines
  ["xs :: List(Int)"
  ,"xs = [1,2,3]"
  ]

listGraph :: Graph
listGraph =
  (fromList
   [("xs"
    ,BratNode Id [("a1", List (SimpleTy IntTy))] [("a1", List (SimpleTy IntTy))])
   ,("mklist.tail.tail"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", List (SimpleTy IntTy))
     ]
     [("value", List (SimpleTy IntTy))]
    )
   ,("mklist.tail"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", List (SimpleTy IntTy))
     ]
     [("value", List (SimpleTy IntTy))]
    )
   ,("mklist"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", SimpleTy IntTy)
     ]
     [("value", List (SimpleTy IntTy))]
    )
   ,("nil", BratNode (Constructor DNil) [] [("value", List (SimpleTy IntTy))])
   ,("1", BratNode (Const (Num 1)) [] [("value", SimpleTy IntTy)])
   ,("2", BratNode (Const (Num 2)) [] [("value", SimpleTy IntTy)])
   ,("3", BratNode (Const (Num 3)) [] [("value", SimpleTy IntTy)])
   ]
  ,[(("1", "value"), Right (SimpleTy IntTy), ("mklist", "head"))
   ,(("2", "value"), Right (SimpleTy IntTy), ("mklist.tail", "head"))
   ,(("3", "value"), Right (SimpleTy IntTy), ("mklist.tail.tail", "head"))
   ,(("nil", "value"), Right (List (SimpleTy IntTy)), ("mklist.tail.tail", "tail"))
   ,(("mklist.tail.tail", "value"), Right (List (SimpleTy IntTy)), ("mklist.tail", "tail"))
   ,(("mklist.tail", "value"), Right (List (SimpleTy IntTy)), ("mklist", "tail"))
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

vecGraph :: Graph
vecGraph =
  (fromList
   [("xs"
    ,BratNode Id
    [("a1", Vector (SimpleTy IntTy) (Simple (Num 3)))]
    [("a1", Vector (SimpleTy IntTy) (Simple (Num 3)))]
    )
   ,("mkvec"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", Vector (SimpleTy IntTy) (Simple (Num 2)))
     ]
     [("value", Vector (SimpleTy IntTy) (Simple (Num 3)))]
    )
   ,("mkvec.tail"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", Vector (SimpleTy IntTy) (Simple (Num 1)))
     ]
     [("value", Vector (SimpleTy IntTy) (Simple (Num 2)))]
    )
   ,("mkvec.tail.tail"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", Vector (SimpleTy IntTy) (Simple (Num 0)))
     ]
     [("value", Vector (SimpleTy IntTy) (Simple (Num 1)))]
    )
   ,("nil", BratNode (Constructor DNil) [] [("value", Vector (SimpleTy IntTy) (Simple (Num 0)))])
   ,("0", BratNode (Const (Num 0)) [] [("value", SimpleTy IntTy)])
   ,("1", BratNode (Const (Num 1)) [] [("value", SimpleTy IntTy)])
   ,("2", BratNode (Const (Num 2)) [] [("value", SimpleTy IntTy)])
   -- This is for the type of the vectors
   ,("0n", BratNode (Const (Num 0)) [] [("value", SimpleTy Natural)])
   ,("1n", BratNode (Const (Num 1)) [] [("value", SimpleTy Natural)])
   ,("2n", BratNode (Const (Num 2)) [] [("value", SimpleTy Natural)])
   ,("3n", BratNode (Const (Num 3)) [] [("value", SimpleTy Natural)])
   ,("hypo0", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("hypo1", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("hypo2", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("hypo3", BratNode Hypo [("value", SimpleTy Natural)] [])
   ]
  ,[(("0", "value"), Right (SimpleTy IntTy), ("mkvec", "head"))
   ,(("1", "value"), Right (SimpleTy IntTy), ("mkvec.tail", "head"))
   ,(("2", "value"), Right (SimpleTy IntTy), ("mkvec.tail.tail", "head"))
   ,(("mkvec.tail", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), ("mkvec", "tail"))
   ,(("mkvec.tail.tail", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 1))), ("mkvec.tail", "tail"))
   ,(("nil", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 0))), ("mkvec.tail.tail", "tail"))

   ,(("0n", "value"), Right (SimpleTy Natural), ("hypo0", "value"))
   ,(("1n", "value"), Right (SimpleTy Natural), ("hypo1", "value"))
   ,(("2n", "value"), Right (SimpleTy Natural), ("hypo2", "value"))
   ,(("3n", "value"), Right (SimpleTy Natural), ("hypo3", "value"))
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

pairGraph :: Graph
pairGraph =
  (fromList
   [("xs"
    ,BratNode Id
     [("a1", Product (SimpleTy IntTy) (SimpleTy Boolean))]
     [("a1", Product (SimpleTy IntTy) (SimpleTy Boolean))]
    )
   ,("mkpair"
    ,BratNode (Constructor DPair)
     [("first", SimpleTy IntTy)
     ,("second", SimpleTy Boolean)
     ]
     [("value", Product (SimpleTy IntTy) (SimpleTy Boolean))]
    )
   ,("1", BratNode (Const (Num 1)) [] [("value", SimpleTy IntTy)])
   ,("true", BratNode (Const (Bool True)) [] [("value", SimpleTy Boolean)])
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

consGraph :: Graph
consGraph =
  (fromList
   [("three"
    ,BratNode Id
     [("a1", Vector (SimpleTy IntTy) (Simple (Num 3)))]
     [("a1", Vector (SimpleTy IntTy) (Simple (Num 3)))]
    )
   ,("two"
    ,BratNode Id
     [("a1", Vector (SimpleTy IntTy) (Simple (Num 2)))]
     [("a1", Vector (SimpleTy IntTy) (Simple (Num 2)))]
    )

   ,("three.vec.cons"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", Vector (SimpleTy IntTy) (Simple (Num 2)))
     ]
     [("value", Vector (SimpleTy IntTy) (Simple (Num 3)))]
    )

   ,("two.vec.cons"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", Vector (SimpleTy IntTy) (Simple (Num 1)))
     ]
     [("value", Vector (SimpleTy IntTy) (Simple (Num 2)))]
    )

   ,("two.vec.cons.tail"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", Vector (SimpleTy IntTy) (Simple (Num 0)))
     ]
     [("value", Vector (SimpleTy IntTy) (Simple (Num 1)))]
    )

   ,("nil", BratNode (Constructor DNil) [] [("value", Vector (SimpleTy IntTy) (Simple (Num 0)))])
   ,("0", BratNode (Const (Num 0)) [] [("value", SimpleTy IntTy)])
   ,("1", BratNode (Const (Num 1)) [] [("value", SimpleTy IntTy)])
   ,("2", BratNode (Const (Num 2)) [] [("value", SimpleTy IntTy)])
   ,("0n", BratNode (Const (Num 0)) [] [("value", SimpleTy Natural)])
   ,("1n", BratNode (Const (Num 1)) [] [("value", SimpleTy Natural)])
   ,("2n", BratNode (Const (Num 2)) [] [("value", SimpleTy Natural)])
   ,("3n", BratNode (Const (Num 3)) [] [("value", SimpleTy Natural)])
   ,("hypo0", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("hypo1", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("hypo2", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("hypo3", BratNode Hypo [("value", SimpleTy Natural)] [])
   ]
  ,[(("0", "value"), Right (SimpleTy IntTy), ("three.vec.cons", "head"))
   ,(("1", "value"), Right (SimpleTy IntTy), ("two.vec.cons", "head"))
   ,(("2", "value"), Right (SimpleTy IntTy), ("two.vec.cons.tail", "head"))
   ,(("nil", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 0))), ("two.vec.cons.tail", "tail"))
   ,(("two.vec.cons.tail", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 1))), ("two.vec.cons", "tail"))
   ,(("two", "a1"), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), ("two.vec.cons", "tail"))
   ,(("0n", "value"), Right (SimpleTy Natural), ("hypo0", "value"))
   ,(("1n", "value"), Right (SimpleTy Natural), ("hypo1", "value"))
   ,(("2n", "value"), Right (SimpleTy Natural), ("hypo2", "value"))
   ,(("3n", "value"), Right (SimpleTy Natural), ("hypo3", "value"))
   ,(("two.vec.cons", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), ("two", "a1"))
   ,(("three.vec.cons", "value"), Right (Vector (SimpleTy IntTy) (Simple (Num 3))), ("three", "a1"))
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

numGraph :: Graph
numGraph =
  (fromList
   [("n"
    ,BratNode Id
      [("a1", SimpleTy Natural)]
      [("a1", SimpleTy Natural)]
    )
   ,("m"
    ,BratNode Id
     [("a1", SimpleTy IntTy)]
     [("a1", SimpleTy IntTy)]
    )

   ,("succ"
    ,BratNode (Constructor DSucc)
     [("value", SimpleTy Natural)]
     [("value", SimpleTy Natural)]
    )

   ,("doub"
    ,BratNode (Constructor DDoub)
     [("value", SimpleTy IntTy)]
     [("value", SimpleTy IntTy)]
    )

   ,("2", BratNode (Const (Num 2)) [] [("value", SimpleTy Natural)])
   ,("-3", BratNode (Const (Num (-3))) [] [("value", SimpleTy IntTy)])
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
  ,"id3 = { q0, q1, q2 => cons(q0, [q1, q2]) }"
  ]

kernelGraph :: Graph
kernelGraph =
  (fromList
   [("id3"
    ,BratNode Id
     [("a1", ktype)]
     [("a1", ktype)]
    )
   ,("vec.cons.tail.tail"
    ,KernelNode (Constructor DCons)
     [("head", Q Qubit), ("tail", Of (Q Qubit) (Simple (Num 0)))]
     [("value", Of (Q Qubit) (Simple (Num 1)))]
    )

   ,("vec.cons.tail"
    ,KernelNode (Constructor DCons)
     [("head", Q Qubit), ("tail", Of (Q Qubit) (Simple (Num 1)))]
     [("value", Of (Q Qubit) (Simple (Num 2)))]
    )

   ,("vec.cons"
    ,KernelNode (Constructor DCons)
     [("head", Q Qubit), ("tail", Of (Q Qubit) (Simple (Num 2)))]
     [("value", Of (Q Qubit) (Simple (Num 3)))]
    )

   ,("src"
    ,KernelNode Source [] [("a1", Q Qubit), ("b1", Q Qubit), ("c1", Q Qubit)]
    )
   ,("tgt"
    ,KernelNode Target [("a1", Of (Q Qubit) (Simple (Num 3)))] []
    )

   ,("kbox"
    ,BratNode ("src" :>>: "tgt") [] [("fun", ktype)]
    )

   ,("0", BratNode (Const (Num 0)) [] [("value", SimpleTy Natural)])
   ,("1", BratNode (Const (Num 1)) [] [("value", SimpleTy Natural)])
   ,("2", BratNode (Const (Num 2)) [] [("value", SimpleTy Natural)])
   ,("3", BratNode (Const (Num 3)) [] [("value", SimpleTy Natural)])
   ,("hypo0", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("hypo1", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("hypo2", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("hypo3", BratNode Hypo [("value", SimpleTy Natural)] [])
   ,("nil", KernelNode (Constructor DNil) [] [("value", Of (Q Qubit) (Simple (Num 0)))])
   ]
  ,[(("src", "a1"), Left (Q Qubit), ("vec.cons", "head"))
   ,(("src", "b1"), Left (Q Qubit), ("vec.cons.tail", "head"))
   ,(("src", "c1"), Left (Q Qubit), ("vec.cons.tail.tail", "head"))

   ,(("nil", "value"), Left (Of (Q Qubit) (Simple (Num 0))), ("vec.cons.tail.tail", "tail"))
   ,(("vec.cons.tail.tail", "value"), Left (Of (Q Qubit) (Simple (Num 1))), ("vec.cons.tail", "tail"))

   ,(("vec.cons.tail", "value"), Left (Of (Q Qubit) (Simple (Num 2))), ("vec.cons", "tail"))
   ,(("vec.cons", "value"), Left (Of (Q Qubit) (Simple (Num 3))), ("tgt", "a1"))

   ,(("kbox", "fun"), Right ktype, ("id3", "a1"))
   ,(("0", "value"), Right (SimpleTy Natural), ("hypo0", "value"))
   ,(("1", "value"), Right (SimpleTy Natural), ("hypo1", "value"))
   ,(("2", "value"), Right (SimpleTy Natural), ("hypo2", "value"))
   ,(("3", "value"), Right (SimpleTy Natural), ("hypo3", "value"))
   ]
  )
 where
  ktype = K (R [("a1", Q Qubit), ("b1", Q Qubit), ("c1", Q Qubit)]) (R [("a1", Of (Q Qubit) (Simple (Num 3)))])

kernelTest = testCase "kernel" $ runProg "kernel" kernelProg kernelGraph

constructorTests = testGroup "Constructors" [listTest,vecTest,pairTest,consTest,numTest,kernelTest]
