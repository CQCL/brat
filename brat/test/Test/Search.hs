{-# LANGUAGE UndecidableInstances #-}

module Test.Search {- (searchTests) -} where

import Brat.Checker (check, Modey(..))
import Brat.FC
import Brat.Naming
import Brat.Search (vsearch)
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.Simple (SimpleTerm(..))
import Hasochism (N(..))
import Util (names)
import Test.Checking (runEmpty)

import Data.Either (isRight)
import Data.Functor ((<&>))
import Test.QuickCheck
import Test.Tasty.QuickCheck (testProperty)
import Test.Tasty
import Brat.Syntax.Value
import Bwd


-- Bounds for row lengths
bounds = (1,5)
-- Max depth of recursive types
maxDepth = 5

row :: Int -> Int -> Gen (Ro Kernel Z Z)
row d n = sequence [ (name,) <$> arbitrarySValue d | name <- take n names ] <&>
          foldr (\this rest -> RPr this rest) R0

arbitrarySValue :: Int -> Gen (Val Z)
arbitrarySValue d = case d of
  1 -> cheap
  d -> oneof [cheap, vec (d - 1)]
 where
  cheap = pure TBit

  vec d = do
    n <- chooseInt bounds
    ty <- arbitrarySValue d
    pure (TVec ty (VNum (NumValue n Constant0))) -- Only the simplest values of `n`


instance Arbitrary (Val Z) where
  arbitrary = chooseInt bounds >>= \n -> row n maxDepth <&> \r -> VFun Kerny (r :->> r)

tokensTypecheck :: Val Z -> Bool
tokensTypecheck kty =
  let kernels = vsearch fc kty in
    case kernels of
      [] -> False
      (k:_) -> case runEmpty (let ?my = Braty in check (WC fc k) ((), [(NamedPort (In src 0) "fun", Right kty)])) of
          Right ((((), ()), ((), unders)), _) -> null unders
          Left _ -> False
 where
  fc = FC (Pos 0 0) (Pos 0 0)
  src = MkName [("src", 0)]

searchTests = testProperty "Token Values Typecheck" tokensTypecheck
