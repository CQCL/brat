{-# LANGUAGE FlexibleContexts #-}

module Test where

import Parser
import Syntax

import Test.HUnit

class Testy (k :: Kind) where
  parser :: String -> Either String (Term Syn k)

instance Testy Verb where
  parser = verb

instance Testy Noun where
  parser = noun

(?=) :: Testy k => String -> Term Syn k -> Test
str ?= expected = TestLabel str . TestCase $
  case parser str of
    Right actual -> actual @?= expected
    Left err     -> assertFailure err
infix 2 ?=

-- chk :: Term Syn Verb -> [(Src, VType)] -> (Outputs Syn, Connectors Syn Verb) -> Test

chk :: (Eq (Overs k), Show (Overs k), Testy k)
    => Term Syn k -> Overs k -> (Outputs Syn, Connectors Syn k) -> Test
chk tm ins expected =
  TestCase $ case go (check tm (ins, ())) of
               Right (actual, _) -> actual @?= expected
               Left er -> assertFailure er

nchk :: Term Syn Verb -> [(Src, VType)] -> (Outputs Syn, Connectors Syn Verb) -> Test
nchk tm ins expected =
  TestCase $ case go (check tm (ins, ())) of
               Right (actual, _) -> actual @?= expected
               Left er -> assertFailure er

tests = TestList
  ["#copy!" ?=
    Do (Fun "copy")

  ,"x -> #copy(x)" ?=
    (Bind "x" :\: (Fun "copy" :$: (Emb (Var "x"))))

  ,"#copy!,#copy!" ?=
    (Do (Fun "copy") :|: Do (Fun "copy"))

  ,"x -> (#copy,#copy)(x)" ?=
    (Bind "x" :\: ((Fun "copy" :|: Fun "copy") :$: (Emb $ Var "x")))

  ,"(#copy,#copy)!;(#id,#swap,#id)!" ?=
    (Do (Fun "copy" :|: Fun "copy")
      :-:
      Do (Fun "id" :|: Fun "swap" :|: Fun "id"))

  ,"x, y -> #swap((y, x))" ?=
    (Bind "x" :||: Bind "y") :\: (Fun "swap" :$: (Emb $ Var "y" :|: Var "x"))

-- NB: port pulling not working
  ,"x, y -> #swap(bjorn:x, y)" ?=
    (Bind "x" :||: Bind "y") :\:
    ((Pull ["bjorn"] $ Emb (Fun "swap" :$: (Emb $ Var "x" :|: Var "y")))
    :::
    ([("annefried", Ty), ("benny", Ty)]))

  ,"bar:x,y -> x, y" ?=
    (APull ["bar"] (Bind "x" :||: Bind "y")) :\: (Var "x" :|: Var "y")
  ,tooBig
--

  ,"x -> #add(#copy(x))" ?=
    Bind "x" :\: (Fun "add" :$: (Emb $ Fun "copy" :$: (Emb $ Var "x")))
  
  -- nouns
  ,"#copy" ?= Fun "copy"
  ,"copy" ?= Var "copy"
  ,"(#copy, #copy)" ?= (Fun "copy" :|: Fun "copy")
  ]
  where
   tooBig =
     let ty = [("x", Ty), ("y", Ty)]
         fun = (Bind "x" :||: Bind "y") :\: (Var "y" :|: Var "x")
         args = Emb (Var "x" :|: Var "y")
         expr = (Bind "x" :||: Bind "y")  :\: (((Th (Emb fun)) ::: ty) :$: args)
     in "x, y -> ({ x, y -> y, x } :: fun: {a: Ty, b: Ty -> c: Ty, d: Ty})(y, x)" ?= expr

total :: Outputs Syn -> (Outputs Syn, Connectors Syn Verb)
total o = (o, ([], ()))

checkTests = TestLabel "checking" $ TestList
  [chk (Do (Fun "copy"))
   [((0, "foo"), Ty)]
   (total [((2, "left"),Ty), ((2, "right"),Ty)])
  ,chk (Bind "x" :\: (Fun "copy" :$: Emb (Var "x")))
   [((0, "foo"), Ty)]
   (total [((2, "left"), Ty), ((2, "right"), Ty)])
  ,chk (Do (Fun "copy") :|: Do (Fun "copy"))
   [((0, "foo"), Ty), ((1, "bar"), Ty)]
   (total [((2, "left"), Ty), ((2, "right"), Ty), ((3, "left"), Ty), ((3, "right"), Ty)])
  ,chk (Bind "x" :\: (Fun "copy" :$: Emb (Var "x")))
   [((0, "foo"), Ty)]
   (total [((2, "left"), Ty), ((2, "right"), Ty)])
  ,chk (Bind "x" :\: (Fun "copy" :$: Emb (Var "x")))
   [((0, "foo"), Ty)]
   (total [((2, "left"), Ty), ((2, "right"), Ty)])

  ,chk (Bind "x" :\: ((Fun "copy" :|: Fun "copy") :$: Emb (Var "x")))
   [((0, "foo"), Ty), ((1, "bar"), Ty)]
   (total [((2, "left"), Ty), ((2, "right"), Ty), ((3, "left"), Ty), ((3, "right"), Ty)])

--   [((0, "foo"), Ty), ((0, "bar"), Ty), ((1, "baz"), Ty)]
--   ([((2, "left"), Ty), ((2, "right"), Ty), ((3, "left"), Ty), ((3, "right"), Ty)]
--   , ([((1, "baz"), Ty)], ()))

  ,chk
   (Do (Fun "copy") :|: Do (Fun "copy"))
   [((0, "foo"), Ty), ((0, "bar"), Ty)]
   (total [((2, "left"), Ty), ((2, "right"), Ty)
          ,((3, "left"), Ty), ((3, "right"), Ty)])

  ,chk
   (Do (Fun "copy" :|: Fun "copy")
    :-:
    Do (Fun "id" :|: Fun "swap" :|: Fun "id"))
    [((0, "foo"), Ty), ((0, "bar"), Ty)]
    (total [((4, "value"), Ty), ((5, "benny"), Ty), ((5, "annefried"), Ty), ((6, "value"), Ty)])

--  ,Bind "x" :||: Bind "y" :\: (Fun "swap" :$: (Emb $ Var "y" :|: Var "x"))
--  ,Bind "x" :||: Bind "y" :\:
--    ((Pull ["bjorn"] $ Emb (Fun "swap" :$: (Emb $ Var "x" :|: Var "y")))
--    :::
--    ([("annefried", Ty), ("benny", Ty)]))
--  ,APull ["bar"] (Bind "x" :||: Bind "y") :\: (Var "x" :|: Var "y")
--  ,Bind "x" :\: (Fun "add" :$: (Emb $ Fun "copy" :$: (Emb $ Var "x")))
  ]

rpl :: IO ()
rpl = do
  putStr ">>> "
  line <- getLine
  case noun line of
    Right expr -> print expr
    Left  er   -> putStrLn er
  rpl

main = runTestTT (TestList [tests, checkTests])

{-
d :: String -> Either String ()
d str = do
  (name, ty, body) <- decl str
  go $ check body ((), ty)
-}
