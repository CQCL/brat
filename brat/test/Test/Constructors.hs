{-# LANGUAGE OverloadedStrings #-}

module Test.Constructors (constructorTests) where

import Brat.Load
import Brat.FC
import Brat.Graph
import Brat.Syntax.Core
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value

import Test.Circuit.Common

import Control.Monad.Except
import Data.Map (fromList)
import Test.Tasty
import Test.Tasty.HUnit

--  FIXME
{-
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
    ,BratNode Id [("a1", List TInt)] [("a1", List TInt)])
   ,("mklist"
    ,BratNode (Constructor DCons)
     [("head", SimpleTy IntTy)
     ,("tail", List (SimpleTy IntTy))
     ]
     [("value", List TInt)]
    )
   ,("nil", BratNode (Constructor DNil) [] [("value", List TInt)])
   ,("1", BratNode (Const (Num 1)) [] [("value", TInt)])
   ,("2", BratNode (Const (Num 2)) [] [("value", TInt)])
   ,("3", BratNode (Const (Num 3)) [] [("value", TInt)])
   ]
  ,[((Ex "1" 0), Right TInt, (In "mklist" 0))
   ,((Ex "2" 0), Right TInt, (In "mklist.tail" 0))
   ,((Ex "3" 0), Right TInt, (In "mklist.tail.tail" 0))
   ,((Ex "nil" 0), Right (TList TInt), (In "mklist.tail.tail" 1))
   ,((Ex "mklist.tail.tail" 0), Right (TList TInt), (In "mklist.tail" 1))
   ,((Ex "mklist.tail" 0), Right (TList TInt), (In "mklist" 1))
   ,((Ex "mklist" 0), Right (TList TInt), (In "xs" 0))
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
    [("a1", Vector (dummyFC TInt) (dummyFC (Simple (Num 3))))]
    [("a1", Vector (dummyFC TInt) (dummyFC (Simple (Num 3))))]
    )
   ,("mkvec"
    ,BratNode (Constructor CVec)
     [("e0", TInt)
     ,("e1", TInt)
     ,("e2", TInt)
     ]
     [("value", Vector (dummyFC $ TInt) (dummyFC $ Simple (Num 3)))]
    )
   ,("0", BratNode (Const (Num 0)) [] [("value", TInt)])
   ,("1", BratNode (Const (Num 1)) [] [("value", TInt)])
   ,("2", BratNode (Const (Num 2)) [] [("value", TInt)])
   -- This is for the type of the vector
   ,("3", BratNode (Const (Num 3)) [] [("value", TNat)])
   ,("hypo", BratNode Hypo [("value", TNat)] [])
   ]
  ,[((Ex "0" 0), Right TInt, ("mkvec", In 0))
   ,((Ex "1" 0), Right TInt, ("mkvec.tail", In 0))
   ,((Ex "2" 0), Right TInt, (In "mkvec.tail.tail" 0))
   ,((Ex "mkvec.tail" 0), Right (TVec TInt (Simple (Num 2))), (In "mkvec" 1))
   ,((Ex "mkvec.tail.tail" 0), Right (TVec TInt (Simple (Num 1))), (In "mkvec.tail" 1))
   ,((Ex "nil" 0), Right (TVec TInt (Simple (Num 0))), (In "mkvec.tail.tail" 1))

   ,((Ex "0n" 0), Right TNat, (In "hypo0" 0))
   ,((Ex "1n" 0), Right TNat, (In "hypo1" 0))
   ,((Ex "2n" 0), Right TNat, (In "hypo2" 0))
   ,((Ex "3n" 0), Right TNat, (In "hypo3" 0))
   ,((Ex "mkvec" 0), Right (TVec TInt (Simple (Num 3))), (In "xs" 0))
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
     [("a1", TCons (dummyFC TInt) (dummyFC TBool))]
     [("a1", TCons (dummyFC TInt) (dummyFC TBool))]
    )
   ,("mkpair"
    ,BratNode (Constructor CPair)
     [("first", TInt)
     ,("second", SimpleTy Boolean)
     ]
     [("value", Product (dummyFC $ TInt) (dummyFC $ TBool))]
    )
   ,("1", BratNode (Const (Num 1)) [] [("value", TInt)])
   ,("true", BratNode (Const (Bool True)) [] [("value", TBool)])
   ]
  ,[((Ex "1" 0),    Right TInt, (In "mkpair" 0))
   ,((Ex "true" 0), Right TBool, (In "mkpair" 1))
   ,((Ex "mkpair" 0), Right (TCons (dummyFC TInt) (dummmyFC TBool)), (In "xs" 0))
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
     [("a1", Vector (dummyFC $ TInt) (dummyFC $ Simple (Num 3)))]
     [("a1", Vector (dummyFC $ TInt) (dummyFC $ Simple (Num 3)))]
    )
   ,("two"
    ,BratNode Id
     [("a1", Vector (dummyFC $ TInt) (dummyFC $ Simple (Num 2)))]
     [("a1", Vector (dummyFC $ TInt) (dummyFC $ Simple (Num 2)))]
    )

   ,("vec.cons"
    ,BratNode (Constructor CCons)
     [("head", TInt)
     ,("tail", Vector (dummyFC $ TInt) (dummyFC $ Simple (Num 2)))
     ]
     [("value", Vector (dummyFC $ TInt) (dummyFC $ Simple (Num 3)))]
    )

   ,("mkvec"
    ,BratNode (Constructor CVec)
     [("e0", TInt)
     ,("e1", TInt)
     ]
     [("value", Vector (dummyFC $ TInt) (dummyFC $ Simple (Num 2)))]
    )

   ,("0", BratNode (Const (Num 0)) [] [("value", TInt)])
   ,("1", BratNode (Const (Num 1)) [] [("value", TInt)])
   ,("2i", BratNode (Const (Num 2)) [] [("value", TInt)])
   ,("2n", BratNode (Const (Num 2)) [] [("value", TNat)])
   ,("3", BratNode (Const (Num 3)) [] [("value", TNat)])
   ,("hypo2", BratNode Hypo [("value", TNat)] [])
   ,("hypo3", BratNode Hypo [("value", TNat)] [])
   ]
  ,[((Ex "0" 0), Right TInt, (In "three.vec.cons" 0))
   ,((Ex "1" 0), Right TInt, (In "two.vec.cons" 0))
   ,((Ex "2" 0), Right TInt, (In "two.vec.cons.tail" 0))
   ,((Ex "nil" 0), Right (TVec TInt (Simple (Num 0))), (In "two.vec.cons.tail" 1))
   ,((Ex "two.vec.cons.tail" 0), Right (TVec TInt (Simple (Num 1))), (In "two.vec.cons" 1))
   ,((Ex "two" 0), Right (TVec TInt (Simple (Num 2))), (In "two.vec.cons" 1))
   ,((Ex "0n" 0), Right TNat, (In "hypo0" 0))
   ,((Ex "1n" 0), Right TNat, (In "hypo1" 0))
   ,((Ex "2n" 0), Right TNat, (In "hypo2" 0))
   ,((Ex "3n" 0), Right TNat, (In "hypo3" 0))
   ,((Ex "two.vec.cons" 0), Right (TVec TInt (Simple (Num 2))), (In "two" 0))
   ,((Ex "three.vec.cons" 0), Right (TVec TInt (Simple (Num 3))), (In "three" 0))
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
      [("a1", TNat)]
      [("a1", TNat)]
    )
   ,("m"
    ,BratNode Id
     [("a1", TInt)]
     [("a1", TInt)]
    )

   ,("succ"
    ,BratNode (Constructor CSucc)
     [("value", TNat)]
     [("value", TNat)]
    )

   ,("doub"
    ,BratNode (Constructor CDoub)
     [("value", TInt)]
     [("value", TInt)]
    )

   ,("2", BratNode (Const (Num 2)) [] [("value", TNat)])
   ,("-3", BratNode (Const (Num (-3))) [] [("value", TInt)])
   ]
  ,[((Ex "2" 0), Right TNat, (In "succ" 0))
   ,((Ex "succ" 0), Right TNat, (In "n" 0))
   ,((Ex "-3" 0), Right TInt, (In "doub" 0))
   ,((Ex "doub" 0), Right TInt, (In "m" 0))
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

   ,("2", BratNode (Const (Num 2)) [] [("value", TNat)])
   ,("3", BratNode (Const (Num 3)) [] [("value", TNat)])
   ,("hypo2", BratNode Hypo [("value", TNat)] [])
   ,("hypo3", BratNode Hypo [("value", TNat)] [])
   ]
  ,[((Ex "src" 0), Left (Q Qubit), (In "vec.cons" 0))
   ,((Ex "src" 1), Left (Q Qubit), (In "vec.cons.tail" 0))
   ,((Ex "src" 2), Left (Q Qubit), (In "vec.cons.tail.tail" 0))

   ,((Ex "nil" 0), Left (Of (Q Qubit) (Simple (Num 0))), (In "vec.cons.tail.tail" 1))
   ,((Ex "vec.cons.tail.tail" 0), Left (Of (Q Qubit) (Simple (Num 1))), (In "vec.cons.tail" 1))
   ,((Ex "vec.cons.tail" 0), Left (Of (Q Qubit) (Simple (Num 2))), (In "vec.cons" 1))
   ,((Ex "vec.cons" 0), Left (Of (Q Qubit) (Simple (Num 3))), (In "tgt" 0))
   ,((Ex "2" 0), Right TNat, (In "hypo2" 0))
   ,((Ex "3" 0), Right TNat, (In "hypo3" 0))
   ]
  )
 where
  ktype = K (R [("a1", Q Qubit), ("b1", Q Qubit), ("c1", Q Qubit)]) (R [("a1", Of (Q Qubit) (Simple (Num 3)))])

kernelTest = testCase "kernel" $ runProg "kernel" kernelProg kernelGraph

-}
constructorTests = testGroup "Constructors" []
