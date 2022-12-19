{-# LANGUAGE OverloadedStrings #-}

module Test.Constructors (constructorTests) where

import Brat.Load
import Brat.Graph
import Brat.Syntax.Core
import Brat.Syntax.Common
import Brat.Syntax.Simple

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
     ,("tail", List (SimpleTy IntTy))
     ]
     [("value", List (SimpleTy IntTy))]
    )
   ,("nil", BratNode (Constructor DNil) [] [("value", List (SimpleTy IntTy))])
   ,("1", BratNode (Const (Num 1)) [] [("value", SimpleTy IntTy)])
   ,("2", BratNode (Const (Num 2)) [] [("value", SimpleTy IntTy)])
   ,("3", BratNode (Const (Num 3)) [] [("value", SimpleTy IntTy)])
   ]
  ,[((Ex "1" 0), Right (SimpleTy IntTy), (In "mklist" 0))
   ,((Ex "2" 0), Right (SimpleTy IntTy), (In "mklist.tail" 0))
   ,((Ex "3" 0), Right (SimpleTy IntTy), (In "mklist.tail.tail" 0))
   ,((Ex "nil" 0), Right (List (SimpleTy IntTy)), (In "mklist.tail.tail" 1))
   ,((Ex "mklist.tail.tail" 0), Right (List (SimpleTy IntTy)), (In "mklist.tail" 1))
   ,((Ex "mklist.tail" 0), Right (List (SimpleTy IntTy)), (In "mklist" 1))
   ,((Ex "mklist" 0), Right (List (SimpleTy (IntTy))), (In "xs" 0))
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
  ,[((Ex "0" 0), Right (SimpleTy IntTy), (In "mkvec" 0))
   ,((Ex "1" 0), Right (SimpleTy IntTy), (In "mkvec.tail" 0))
   ,((Ex "2" 0), Right (SimpleTy IntTy), (In "mkvec.tail.tail" 0))
   ,((Ex "mkvec.tail" 0), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), (In "mkvec" 1))
   ,((Ex "mkvec.tail.tail" 0), Right (Vector (SimpleTy IntTy) (Simple (Num 1))), (In "mkvec.tail" 1))
   ,((Ex "nil" 0), Right (Vector (SimpleTy IntTy) (Simple (Num 0))), (In "mkvec.tail.tail" 1))

   ,((Ex "0n" 0), Right (SimpleTy Natural), (In "hypo0" 0))
   ,((Ex "1n" 0), Right (SimpleTy Natural), (In "hypo1" 0))
   ,((Ex "2n" 0), Right (SimpleTy Natural), (In "hypo2" 0))
   ,((Ex "3n" 0), Right (SimpleTy Natural), (In "hypo3" 0))
   ,((Ex "mkvec" 0), Right (Vector (SimpleTy IntTy) (Simple (Num 3))), (In "xs" 0))
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
  ,[((Ex "1" 0),    Right (SimpleTy IntTy), (In "mkpair" 0))
   ,((Ex "true" 0), Right (SimpleTy Boolean), (In "mkpair" 1))
   ,((Ex "mkpair" 0), Right (Product (SimpleTy IntTy) (SimpleTy Boolean)), (In "xs" 0))
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
  ,[((Ex "0" 0), Right (SimpleTy IntTy), (In "three.vec.cons" 0))
   ,((Ex "1" 0), Right (SimpleTy IntTy), (In "two.vec.cons" 0))
   ,((Ex "2" 0), Right (SimpleTy IntTy), (In "two.vec.cons.tail" 0))
   ,((Ex "nil" 0), Right (Vector (SimpleTy IntTy) (Simple (Num 0))), (In "two.vec.cons.tail" 1))
   ,((Ex "two.vec.cons.tail" 0), Right (Vector (SimpleTy IntTy) (Simple (Num 1))), (In "two.vec.cons" 1))
   ,((Ex "two" 0), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), (In "two.vec.cons" 1))
   ,((Ex "0n" 0), Right (SimpleTy Natural), (In "hypo0" 0))
   ,((Ex "1n" 0), Right (SimpleTy Natural), (In "hypo1" 0))
   ,((Ex "2n" 0), Right (SimpleTy Natural), (In "hypo2" 0))
   ,((Ex "3n" 0), Right (SimpleTy Natural), (In "hypo3" 0))
   ,((Ex "two.vec.cons" 0), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), (In "two" 0))
   ,((Ex "three.vec.cons" 0), Right (Vector (SimpleTy IntTy) (Simple (Num 3))), (In "three" 0))
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
  ,[((Ex "2" 0), Right (SimpleTy Natural), (In "succ" 0))
   ,((Ex "succ" 0), Right (SimpleTy Natural), (In "n" 0))
   ,((Ex "-3" 0), Right (SimpleTy IntTy), (In "doub" 0))
   ,((Ex "doub" 0), Right (SimpleTy IntTy), (In "m" 0))
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
  ,[((Ex "src" 0), Left (Q Qubit), (In "vec.cons" 0))
   ,((Ex "src" 1), Left (Q Qubit), (In "vec.cons.tail" 0))
   ,((Ex "src" 2), Left (Q Qubit), (In "vec.cons.tail.tail" 0))

   ,((Ex "nil" 0), Left (Of (Q Qubit) (Simple (Num 0))), (In "vec.cons.tail.tail" 1))
   ,((Ex "vec.cons.tail.tail" 0), Left (Of (Q Qubit) (Simple (Num 1))), (In "vec.cons.tail" 1))

   ,((Ex "vec.cons.tail" 0), Left (Of (Q Qubit) (Simple (Num 2))), (In "vec.cons" 1))
   ,((Ex "vec.cons" 0), Left (Of (Q Qubit) (Simple (Num 3))), (In "tgt" 0))

   ,((Ex "kbox" 0), Right ktype, (In "id3" 0))
   ,((Ex "0" 0), Right (SimpleTy Natural), (In "hypo0" 0))
   ,((Ex "1" 0), Right (SimpleTy Natural), (In "hypo1" 0))
   ,((Ex "2" 0), Right (SimpleTy Natural), (In "hypo2" 0))
   ,((Ex "3" 0), Right (SimpleTy Natural), (In "hypo3" 0))
   ]
  )
 where
  ktype = K (R [("a1", Q Qubit), ("b1", Q Qubit), ("c1", Q Qubit)]) (R [("a1", Of (Q Qubit) (Simple (Num 3)))])

kernelTest = testCase "kernel" $ runProg "kernel" kernelProg kernelGraph

constructorTests = testGroup "Constructors" [listTest,vecTest,pairTest,consTest,numTest,kernelTest]
