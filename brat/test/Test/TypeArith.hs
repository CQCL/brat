-- Test our ability to do arithmetic in types
module Test.TypeArith where

import Brat.Checker.Helpers (runArith)
import Brat.FC
import Brat.Naming (Name(..))
import Brat.Syntax.Common (ArithOp(..), TypeKind(Nat))
import Brat.Syntax.Port
import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.Syntax.Value
import Hasochism (N(..), Ny(..), Some(..), (:*)(..))

import Data.List (sort)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding ((^))

-- A dummy variable to make NumVals with
var = VPar (ExEnd (Ex (MkName []) 0))

instance Arbitrary (NumVal (VVar Z)) where
  arbitrary = NumValue <$> (abs <$> arbitrary) <*> arbitrary

instance Arbitrary (Fun00 (VVar Z)) where
  arbitrary = sized aux
   where
    aux 0 = pure Constant0
    aux n = oneof [pure Constant0, StrictMonoFun <$> resize (n `div` 2) arbitrary]

instance Arbitrary (StrictMono (VVar Z)) where
  arbitrary = StrictMono <$> (abs <$> arbitrary) <*> arbitrary

instance Arbitrary (Monotone (VVar Z)) where
  arbitrary = sized aux
   where
    aux 0 = pure (Linear var)
    aux n = oneof [Full <$> resize (n `div` 2) arbitrary, pure (Linear var)]

adding = testProperty "adding" $ \x a' b' ->
  let (a, b) = (abs a', abs b')
      lhs = NumValue a x
      rhs = NumValue b x
  in Just (NumValue (a + b) x) == runArith lhs Add rhs

subtractEq = testProperty "subtract equal Fun00" $ \x a' b' ->
  let [b, a] = sort [abs a', abs b']
      lhs = NumValue a x
      rhs = NumValue b x
  in Just (NumValue (a - b) Constant0) == runArith lhs Sub rhs

subtractConst = testProperty "subtract const" $ \x a' b' ->
  let [b, a] = sort [abs a', abs b']
      lhs = NumValue a x
      rhs = NumValue b Constant0
  in Just (NumValue (a - b) x) == runArith lhs Sub rhs

subtractFactorOf2 = testProperty "subtract factor of 2" $ \x a' b' ->
  let [b, a] = sort [abs a', abs b']
      lhs = nPlus a (n2PowTimes 1 (NumValue 0 x))
      rhs = NumValue b x
  in Just (NumValue (a - b) x) == runArith lhs Sub rhs

multiplyByPowerOf2 = testProperty "multiply by a power of 2" $ \x k' b' coin ->
  let (k, b) = (abs k', abs b')
      a = 2 ^ k
      -- This should be commutative, so flip the arguments sometimes
      (lhs, rhs) = if coin
                   then (NumValue a Constant0, NumValue b x)
                   else (NumValue b x, NumValue a Constant0)
      NumValue 0 x' = n2PowTimes k (NumValue 0 x)
  in  Just (NumValue (a * b) x') == runArith lhs Mul rhs

exponentiateConst = testProperty "exponentiate constants" $ \a' b' ->
  let (a, b) = (abs a', abs b')
      lhs = NumValue a Constant0
      rhs = NumValue b Constant0
  in  Just (NumValue (a ^ b) Constant0) == runArith lhs Pow rhs

exponentiatePow2 = testCase "(2^(2^k)) ^ n" $ assertEqual "" -- k = 2; 2^k = 4; 2^(2^k) = 16
  (runArith (nConstant 16) Pow (nVar var)) -- (2 ^ (2 ^ 4))^n
  (Just (NumValue 1 (StrictMonoFun (StrictMono 0 (Full (StrictMono 2 (Linear var))))))) -- 1 + ((2^k * n) - 1) = 2 ^ 4n

typeArithTests = testGroup "Type Arithmetic"
  [adding
  ,subtractEq
  ,subtractConst
  ,subtractFactorOf2
  ,multiplyByPowerOf2
  ,exponentiateConst
  ,exponentiatePow2
  ]
