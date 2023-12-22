{-# LANGUAGE OverloadedStrings #-}

module Test.Constructors (constructorTests) where

import Brat.Constructors (pattern CNil
                         ,pattern CCons
                         ,pattern CSucc
                         ,pattern CDoub
                         ,pattern CTrue
                         ,pattern CVec
                         ,pattern CInt
                         ,pattern CNat
                         ,pattern CBool
                         )
import Brat.Load
import Brat.FC
import Brat.Graph
import Brat.Syntax.Core
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName

import Test.Circuit.Common

import Control.Monad.Except
import Data.Map (fromList, empty)
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
    ,BratNode Id [("a1", TList TInt)] [("a1", TList TInt)])
   ,("cons"
    ,BratNode (Constructor CCons)
     [("head", TInt)
     ,("tail", TList TInt)
     ]
     [("value", TList TInt)]
    )
   ,("cons.tail"
    ,BratNode (Constructor CCons)
     [("head", TInt)
     ,("tail", TList TInt)
     ]
     [("value", TList TInt)]
    )
   ,("cons.tail.tail"
    ,BratNode (Constructor CCons)
     [("head", TInt)
     ,("tail", TList TInt)
     ]
     [("value", TList TInt)]
    )
   ,("nil", BratNode (Constructor CNil) [] [("value", TList TInt)])
   ,("1", BratNode (Const (Num 1)) [] [("value", TInt)])
   ,("2", BratNode (Const (Num 2)) [] [("value", TInt)])
   ,("3", BratNode (Const (Num 3)) [] [("value", TInt)])
   -- Kind checking
   ,("List", BratNode (Constructor (plain "List"))
    [("listValue", TUnit)]
    [("value", TUnit)]
    )
   ,("Int", BratNode (Constructor (plain "Int"))
    []
    [("value", TUnit)]
    )
   ]
  ,[(Ex "1" 0, Right TInt, In "cons" 0)
   ,(Ex "2" 0, Right TInt, In "cons.tail" 0)
   ,(Ex "3" 0, Right TInt, In "cons.tail.tail" 0)
   ,(Ex "nil" 0, Right (TList TInt), In "cons.tail.tail" 1)
   ,(Ex "cons.tail.tail" 0, Right (TList TInt), In "mklist.tail" 1)
   ,(Ex "cons.tail" 0, Right (TList TInt), In "mklist" 1)
   ,(Ex "cons" 0, Right (TList TInt), In "xs" 0)
   ,(Ex "Int" 0, Right TUnit, In "List" 0)
   -- This node doesn't exist!
   ,(Ex "List" 0, Right TUnit, In "__kca" 0)
   ]
  )

listTest = graphTest "list" listProg listGraph

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
    [("a1", TVec TInt (VNum (nConstant 3)))]
    [("a1", TVec TInt (VNum (nConstant 3)))]
    )
   ,("0", BratNode (Const (Num 0)) [] [("value", TInt)])
   ,("1", BratNode (Const (Num 1)) [] [("value", TInt)])
   ,("2", BratNode (Const (Num 2)) [] [("value", TInt)])
   -- This is for the type of the vector in the program
   ,("3", BratNode (Const (Num 3)) [] [("value", TNat)])
   ,("nil", BratNode (Constructor CNil) [] [("value", TVec TInt (VNum nZero))])
   ,("cons.tail.tail", BratNode (Constructor CCons) [("head", TInt), ("tail", TVec TInt (VNum nZero))] [("value", TVec TInt (VNum $ nConstant 1))])
   ,("cons.tail", BratNode (Constructor CCons) [("head", TInt), ("tail", TVec TInt (VNum $ nConstant 1))] [("value", TVec TInt (VNum $ nConstant 2))])
   ,("cons", BratNode (Constructor CCons) [("head", TInt), ("tail", TVec TInt (VNum $ nConstant 2))] [("value", TVec TInt (VNum $ nConstant 3))])
   ,("Int", BratNode (Constructor CInt) [] [("value", TUnit)])
   ,("Vec", BratNode (Constructor CVec) [("X", TUnit), ("n", TNat)] [("value", TUnit)])
   ]
  ,[(Ex "0" 0, Right TInt, In "mkvec" 0)
   ,(Ex "1" 0, Right TInt, In "mkvec.tail" 0)
   ,(Ex "2" 0, Right TInt, In "mkvec.tail.tail" 0)
   ,(Ex "mkvec.tail" 0, Right (TVec TInt (VNum (nConstant 2))), In "mkvec" 1)
   ,(Ex "mkvec.tail.tail" 0, Right (TVec TInt (VNum (nConstant 1))), In "mkvec.tail" 1)
   ,(Ex "nil" 0, Right (TVec TInt (VNum nZero)), In "mkvec.tail.tail" 1)
   ,(Ex "Int" 0, Right TUnit, In "Vec" 0)
   ,(Ex "3" 0, Right TNat, In "Vec" 1)
   ,(Ex "mkvec" 0, Right (TVec TInt (VNum (nConstant 3))), In "xs" 0)
   -- This isn't in the list of nodes above
   ,(Ex "Vec" 0, Right TUnit, In "__kca" 0)
   ]
  )

vecTest = graphTest "vec" vecProg vecGraph

pairProg :: String
pairProg =
  unlines
  ["xs :: [Int, Bool]"
  ,"xs = [1,true]"
  ]

pairGraph :: Graph
pairGraph = (fromList
   -- These nodes are produced by kindCheck
   [("kc_Bool",
     BratNode (Constructor CBool)
     []
     [("value", TUnit)]
    )
   ,("kc_Int",
     BratNode (Constructor CInt)
     []
     [("value", TUnit)]
    )
   ,("kc_nil",
     BratNode (Constructor CNil)
     []
     [("value", TUnit)]
    )
   -- When kind checking each of our cons types we come up with these nodes with
   -- unit inputs and outputs (Unit because the type arguments are erased in the graph)
   ,("kc_cons_tail",
     BratNode (Constructor CCons)
     [("head", TUnit), ("tail", TUnit)]
     [("value", TUnit)]
    )
   ,("kc_cons",
     BratNode (Constructor CCons)
     [("head", TUnit), ("tail", TUnit)]
     [("value", TUnit)]
    )
   -- Now for the nodes created by type checking
   ,("xs"
    ,BratNode Id
     [("a1", TCons TInt (TCons TBool TUnit))]
     [("a1", TCons TInt (TCons TBool TUnit))]
    )
   ,("mkpair"
    ,BratNode (Constructor CCons)
     [("head", TInt)
     ,("tail", TCons TBool TNil)
     ]
     [("value", TCons TInt (TCons TBool TNil))]
    )
   ,("mkpair_tail"
    ,BratNode (Constructor CCons)
     [("head", TBool)
     ,("tail", TNil)
     ]
     [("value", TCons TBool TNil)]
    )
   ,("nil"
    ,BratNode (Constructor CNil)
     []
     [("value", TNil)]
    )
   ,("1", BratNode (Const (Num 1)) [] [("value", TInt)])
   ,("true", BratNode (Constructor CTrue) [] [("value", TBool)])
   ]
  ,[(Ex "kc_Bool" 0, Right TUnit, In "kc_cons_tail" 0)
   ,(Ex "kc_nil" 0, Right TUnit, In "kc_cons_tail" 1)
   ,(Ex "kc_Int" 0, Right TUnit, In "kc_cons" 0)
   ,(Ex "kc_cons_tail" 0, Right TUnit, In "kc_cons" 1)
   ,(Ex "nil" 0, Right TNil, In "mkpair_tail" 1)
   ,(Ex "true" 0, Right TBool, In "mkpair_tail" 0)
   ,(Ex "1" 0,    Right TInt, In "mkpair" 0)
   ,(Ex "mkpair_tail" 0, Right (TCons TBool TNil), In "mkpair" 1)
   ,(Ex "mkpair" 0, Right (TCons TInt (TCons TBool TNil)), In "xs" 0)
   -- This kc_ann isn't in our node list!
   ,(Ex "kc_cons" 0, Right TUnit, In "kc_ann" 0)
   ]
  )

pairTest = graphTest "pair" pairProg pairGraph

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
     [("a1", TVec TInt (VNum (nConstant 3)))]
     [("a1", TVec TInt (VNum (nConstant 3)))]
    )
   ,("two"
    ,BratNode Id
     [("a1", TVec TInt (VNum (nConstant 2)))]
     [("a1", TVec TInt (VNum (nConstant 2)))]
    )

   ,("vec.cons"
    ,BratNode (Constructor CCons)
     [("head", TInt)
     ,("tail", TVec TInt (VNum (nConstant 2)))
     ]
     [("value", TVec TInt (VNum (nConstant 3)))]
    )

   ,("vec.cons.tail"
    ,BratNode (Constructor CCons)
     [("head", TInt)
     ,("tail", TVec TInt (VNum (nConstant 1)))
     ]
     [("value", TVec TInt (VNum (nConstant 2)))]
    )
   ,("vec.cons.tail.tail"
    ,BratNode (Constructor CCons)
     [("head", TInt)
     ,("tail", TVec TInt (VNum (nConstant 0)))
     ]
     [("value", TVec TInt (VNum (nConstant 1)))]
    )
   ,("nil"
    ,BratNode (Constructor CNil)
     []
     [("value", TVec TInt (VNum (nConstant 0)))]
    )

   -- Kind checking
   ,("Vec1", BratNode (Constructor CVec) [("X", TUnit), ("n", TNat)] [("value", TUnit)])
   ,("Vec2", BratNode (Constructor CVec) [("X", TUnit), ("n", TNat)] [("value", TUnit)])
   ,("Int1", BratNode (Constructor CInt) [] [("value", TUnit)])
   ,("Int2", BratNode (Constructor CInt) [] [("value", TUnit)])
   ,("0i", BratNode (Const (Num 0)) [] [("value", TInt)])
   ,("1i", BratNode (Const (Num 1)) [] [("value", TInt)])
   ,("2i", BratNode (Const (Num 2)) [] [("value", TInt)])
   ,("2n", BratNode (Const (Num 2)) [] [("value", TNat)])
   ,("3n", BratNode (Const (Num 3)) [] [("value", TNat)])
   ]
  ,[(Ex "0i" 0, Right TInt, In "three.vec.cons" 0)
   ,(Ex "1i" 0, Right TInt, In "two.vec.cons" 0)
   ,(Ex "2i" 0, Right TInt, In "two.vec.cons.tail" 0)
   ,(Ex "nil" 0, Right (TVec TInt (VNum nZero)), In "two.vec.cons.tail" 1)
   ,(Ex "two.vec.cons.tail" 0, Right (TVec TInt (VNum (nConstant 1))), In "two.vec.cons" 1)
   ,(Ex "two" 0, Right (TVec TInt (VNum (nConstant 2))), In "two.vec.cons" 1)
   ,(Ex "two.vec.cons" 0, Right (TVec TInt (VNum (nConstant 2))), In "two" 0)
   ,(Ex "three.vec.cons" 0, Right (TVec TInt (VNum (nConstant 3))), In "three" 0)
   -- Kind checking
   ,(Ex "Int1" 0, Right TUnit, In "Vec1" 0)
   ,(Ex "2n" 0, Right TNat, In "Vec1" 1)
   ,(Ex "Int2" 0, Right TUnit, In "Vec2" 0)
   ,(Ex "3n" 0, Right TNat, In "Vec2" 1)
    -- These nodes aren't defined above
   ,(Ex "Vec1" 0, Right TUnit, In "__kca_1" 0)
   ,(Ex "Vec2" 0, Right TUnit, In "__kca_2" 0)
   ]
  )

consTest = graphTest "cons" consProg consGraph

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
   -- Kind checking
   ,("Nat", BratNode (Constructor CNat) [] [("value", TUnit)])
   ,("Int", BratNode (Constructor CInt) [] [("value", TUnit)])
   ]
  ,[(Ex "2" 0, Right TNat, In "succ" 0)
   ,(Ex "succ" 0, Right TNat, In "n" 0)
   ,(Ex "-3" 0, Right TInt, In "doub" 0)
   ,(Ex "doub" 0, Right TInt, In "m" 0)
   -- kind checking nodes that aren't in the above list
   ,(Ex "Nat" 0, Right TUnit, In "__kca_n" 0)
   ,(Ex "Int" 0, Right TUnit, In "__kca_m" 0)
   ]
  )

numTest = graphTest "num" numProg numGraph

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
   ,("nil"
    ,KernelNode (Constructor CNil)
     []
     [("value", VOf VQ nZero)]
    )
   ,("vec.cons.tail.tail"
    ,KernelNode (Constructor CCons)
     [("head", VQ), ("tail", VOf VQ nZero)]
     [("value", VOf VQ (nConstant 1))]
    )

   ,("vec.cons.tail"
    ,KernelNode (Constructor CCons)
     [("head", VQ), ("tail", VOf VQ (nConstant 1))]
     [("value", VOf VQ (nConstant 2))]
    )

   ,("vec.cons"
    ,KernelNode (Constructor CCons)
     [("head", VQ), ("tail", VOf VQ (nConstant 2))]
     [("value", VOf VQ (nConstant 3))]
    )

   ,("src"
    ,KernelNode Source [] [("a1", VQ), ("b1", VQ), ("c1", VQ)]
    )
   ,("tgt"
    ,KernelNode Target [("a1", VOf VQ (nConstant 3))] []
    )

   ,("kbox"
    ,BratNode ("src" :>>: "tgt") [] [("thunk", ktype)]
    )

   ,("3", BratNode (Const (Num 3)) [] [("value", TNat)])
   ]
  ,[(Ex "src" 0, Left VQ, In "vec.cons" 0)
   ,(Ex "src" 1, Left VQ, In "vec.cons.tail" 0)
   ,(Ex "src" 2, Left VQ, In "vec.cons.tail.tail" 0)

   ,(Ex "nil" 0, Left (VOf VQ nZero), In "vec.cons.tail.tail" 1)
   ,(Ex "vec.cons.tail.tail" 0, Left (VOf VQ (nConstant 1)), In "vec.cons.tail" 1)
   ,(Ex "vec.cons.tail" 0, Left (VOf VQ (nConstant 2)), In "vec.cons" 1)
   ,(Ex "vec.cons" 0, Left (VOf VQ (nConstant 3)), In "tgt" 0)
   ,(Ex "kbox" 0, Right ktype, In "id3" 0)
   -- This node isn't in the list above"
   ,(Ex "3" 0, Right TNat, In "__kca" 0)
   ]
  )
 where
  ktype = VFun Kerny ((RPr ("a1", VQ) (RPr ("b1", VQ) (RPr ("c1", VQ) R0))) :->> (RPr ("a1", VOf VQ (nConstant 3)) R0))

kernelTest = graphTest "kernel" kernelProg kernelGraph

constructorTests = testGroup "Constructors" [listTest, vecTest, pairTest, consTest, numTest, kernelTest]
