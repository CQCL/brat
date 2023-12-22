{-# LANGUAGE PolyKinds #-}

module Hasochism where

import Data.Kind (Type)
import Data.Type.Equality (TestEquality(..), (:~:)(..))

data N = Z | S N
data Ny :: N -> Type where
  Zy :: Ny Z
  Sy :: Ny n -> Ny (S n)

ny2int :: Ny n -> Int
ny2int Zy = 0
ny2int (Sy n) = 1 + ny2int n

instance TestEquality Ny where
  testEquality Zy Zy = Just Refl
  testEquality (Sy n) (Sy m) | Just Refl <- testEquality n m = Just Refl
  testEquality _ _ = Nothing

data Some (t :: a -> Type) :: Type where
  -- Stashing some a
  Some :: t a -> Some t

data (:*) (l :: a -> Type) (r :: a -> Type) :: a -> Type where
  (:*) :: l a -> r a -> (l :* r) a

newtype Flip (t :: a -> b -> Type) (y :: b) (x :: a)
  = Flip { getFlip :: t x y }

instance Show (t a b) => Show (Flip t b a) where
  show = show . getFlip
