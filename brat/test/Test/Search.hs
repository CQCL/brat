{-# LANGUAGE UndecidableInstances #-}

module Test.Search (searchTests) where

import Brat.Checker (check, run, emptyEnv, Modey(..))
import Brat.FC
import Brat.Naming
import Brat.Search (vsearch)
import Brat.Syntax.Common
import Brat.Syntax.Core
import Util (names)

import Data.Either (isRight)
import Data.Functor ((<&>))
import Test.QuickCheck
import Test.Tasty.QuickCheck (testProperty)

-- Bounds for row lengths
bounds = (1,5)
-- Max depth of recursive types
maxDepth = 5

instance Arbitrary (Row Term) where
  arbitrary = chooseInt bounds >>= \n -> row n maxDepth

row :: Int -> Int -> Gen (Row Term)
row d n = R <$> sequence [ (name,) <$> arbitrarySType d | name <- take n names ]

arbitrarySType :: Int -> Gen SType
arbitrarySType d = case d of
  1 -> cheap
  d -> oneof [cheap, vec (d - 1)]

 where
  cheap = pure Bit

  vec d = do
    n <- chooseInt bounds
    ty <- arbitrarySType d
    pure (Of ty (Simple (Num n))) -- Only the simplest values of `n`


instance Arbitrary SType where
  arbitrary = arbitrarySType maxDepth
      
instance Arbitrary VType where
  arbitrary = chooseInt bounds >>= \n -> row n maxDepth <&> \r -> K r r

tokensTypecheck :: VType -> Bool
tokensTypecheck kty =
  let kernels = vsearch fc kty in
    case kernels of
      [] -> False
      (k:_) -> case run (emptyEnv, [], fc)
                    (let ?my = Braty in check (WC fc k) ((), [(((src, Ex, 0), "fun"), kty)])) of
                 Right (((), ((), unders)), _) -> null unders
                 Left _ -> False
 where
  fc = FC (Pos 0 0) (Pos 0 0)
  src = MkName [("src", 0)]
  
searchTests = testProperty "Token Values Typecheck" tokensTypecheck
