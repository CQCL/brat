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
  ,[(("1", Ex 0), Right (SimpleTy IntTy), ("mklist", In 0))
   ,(("2", Ex 0), Right (SimpleTy IntTy), ("mklist.tail", In 0))
   ,(("3", Ex 0), Right (SimpleTy IntTy), ("mklist.tail.tail", In 0))
   ,(("nil", Ex 0), Right (List (SimpleTy IntTy)), ("mklist.tail.tail", In 1))
   ,(("mklist.tail.tail", Ex 0), Right (List (SimpleTy IntTy)), ("mklist.tail", In 1))
   ,(("mklist.tail", Ex 0), Right (List (SimpleTy IntTy)), ("mklist", In 1))
   ,(("mklist", Ex 0), Right (List (SimpleTy (IntTy))), ("xs", In 0))
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
  ,[(("0", Ex 0), Right (SimpleTy IntTy), ("mkvec", In 0))
   ,(("1", Ex 0), Right (SimpleTy IntTy), ("mkvec.tail", In 0))
   ,(("2", Ex 0), Right (SimpleTy IntTy), ("mkvec.tail.tail", In 0))
   ,(("mkvec.tail", Ex 0), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), ("mkvec", In 1))
   ,(("mkvec.tail.tail", Ex 0), Right (Vector (SimpleTy IntTy) (Simple (Num 1))), ("mkvec.tail", In 1))
   ,(("nil", Ex 0), Right (Vector (SimpleTy IntTy) (Simple (Num 0))), ("mkvec.tail.tail", In 1))

   ,(("0n", Ex 0), Right (SimpleTy Natural), ("hypo0", In 0))
   ,(("1n", Ex 0), Right (SimpleTy Natural), ("hypo1", In 0))
   ,(("2n", Ex 0), Right (SimpleTy Natural), ("hypo2", In 0))
   ,(("3n", Ex 0), Right (SimpleTy Natural), ("hypo3", In 0))
   ,(("mkvec", Ex 0), Right (Vector (SimpleTy IntTy) (Simple (Num 3))), ("xs", In 0))
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
  ,[(("1", Ex 0),    Right (SimpleTy IntTy), ("mkpair", In 0))
   ,(("true", Ex 0), Right (SimpleTy Boolean), ("mkpair", In 1))
   ,(("mkpair", Ex 0), Right (Product (SimpleTy IntTy) (SimpleTy Boolean)), ("xs", In 0))
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
  ,[(("0", Ex 0), Right (SimpleTy IntTy), ("three.vec.cons", In 0))
   ,(("1", Ex 0), Right (SimpleTy IntTy), ("two.vec.cons", In 0))
   ,(("2", Ex 0), Right (SimpleTy IntTy), ("two.vec.cons.tail", In 0))
   ,(("nil", Ex 0), Right (Vector (SimpleTy IntTy) (Simple (Num 0))), ("two.vec.cons.tail", In 1))
   ,(("two.vec.cons.tail", Ex 0), Right (Vector (SimpleTy IntTy) (Simple (Num 1))), ("two.vec.cons", In 1))
   ,(("two", Ex 0), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), ("two.vec.cons", In 1))
   ,(("0n", Ex 0), Right (SimpleTy Natural), ("hypo0", In 0))
   ,(("1n", Ex 0), Right (SimpleTy Natural), ("hypo1", In 0))
   ,(("2n", Ex 0), Right (SimpleTy Natural), ("hypo2", In 0))
   ,(("3n", Ex 0), Right (SimpleTy Natural), ("hypo3", In 0))
   ,(("two.vec.cons", Ex 0), Right (Vector (SimpleTy IntTy) (Simple (Num 2))), ("two", In 0))
   ,(("three.vec.cons", Ex 0), Right (Vector (SimpleTy IntTy) (Simple (Num 3))), ("three", In 0))
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
  ,[(("2", Ex 0), Right (SimpleTy Natural), ("succ", In 0))
   ,(("succ", Ex 0), Right (SimpleTy Natural), ("n", In 0))
   ,(("-3", Ex 0), Right (SimpleTy IntTy), ("doub", In 0))
   ,(("doub", Ex 0), Right (SimpleTy IntTy), ("m", In 0))
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
  ,[(("src", Ex 0), Left (Q Qubit), ("vec.cons", In 0))
   ,(("src", Ex 1), Left (Q Qubit), ("vec.cons.tail", In 0))
   ,(("src", Ex 2), Left (Q Qubit), ("vec.cons.tail.tail", In 0))

   ,(("nil", Ex 0), Left (Of (Q Qubit) (Simple (Num 0))), ("vec.cons.tail.tail", In 1))
   ,(("vec.cons.tail.tail", Ex 0), Left (Of (Q Qubit) (Simple (Num 1))), ("vec.cons.tail", In 1))

   ,(("vec.cons.tail", Ex 0), Left (Of (Q Qubit) (Simple (Num 2))), ("vec.cons", In 1))
   ,(("vec.cons", Ex 0), Left (Of (Q Qubit) (Simple (Num 3))), ("tgt", In 0))

   ,(("kbox", Ex 0), Right ktype, ("id3", In 0))
   ,(("0", Ex 0), Right (SimpleTy Natural), ("hypo0", In 0))
   ,(("1", Ex 0), Right (SimpleTy Natural), ("hypo1", In 0))
   ,(("2", Ex 0), Right (SimpleTy Natural), ("hypo2", In 0))
   ,(("3", Ex 0), Right (SimpleTy Natural), ("hypo3", In 0))
   ]
  )
 where
  ktype = K (R [("a1", Q Qubit), ("b1", Q Qubit), ("c1", Q Qubit)]) (R [("a1", Of (Q Qubit) (Simple (Num 3)))])

kernelTest = testCase "kernel" $ runProg "kernel" kernelProg kernelGraph

constructorTests = testGroup "Constructors" [listTest,vecTest,pairTest,consTest,numTest,kernelTest]
