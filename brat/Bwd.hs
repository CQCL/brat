module Bwd where

-- A backwards list, i.e. where cons adds elements to the right
data Bwd a
  = B0
  -- Mnemonic: the `<` is an arrow pointing to the big end of the list
  | Bwd a :< a
 deriving (Eq, Foldable, Functor, Show, Traversable)

{- For symmetry we could define
data Fwd a
  = F0
  | a :> Fwd a
but this is the same as haskell's `[]`, so probably not worth it
-}

instance Semigroup (Bwd a) where
  (<>) = mappend

instance Monoid (Bwd a) where
  mempty = B0
  mappend zx B0 = zx
  mappend zx (zy :< y) = mappend zx zy :< y

-- "Fish" concatenates a Bwd with a list, adding the list elements on the right
-- note that the operator spells out the direction of it's arguments and output
(<><) :: Bwd a -> [a] -> Bwd a
zx <>< [] = zx
zx <>< (x:xs) = zx :< x <>< xs

-- "Chips" does the same thing as fish, but concatenates by adding the Bwd
-- elements to the left of the list argument
(<>>) :: Bwd a -> [a] -> [a]
B0 <>> xs = xs
(zx :< x) <>> xs = zx <>> (x:xs)

findUnder :: Eq a => a -> Bwd a -> Maybe Int
findUnder needle = search 0 where
 search _ B0 = Nothing
 search i (stack :< hay)
  | needle == hay = Just i
  | otherwise = search (i + 1) stack

(!<) :: Bwd a -> Int -> a
B0 !< _ = error "(!<) failed"
(_ :< x) !< 0 = x
(zx :< _) !< i = zx !< (i - 1)

(<+) :: Bwd a -> Bwd a -> Bwd a
zx <+ (zy :< y) = (zx <+ zy) :< y
zx <+ B0 = zx
