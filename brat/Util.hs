module Util where

lookupBy :: (a -> Bool) -> (a -> b) -> [a] -> Maybe b
lookupBy _ _ [] = Nothing
lookupBy p f (x:xs) | p x = Just (f x)
                    | otherwise = lookupBy p f xs

maybeToRight :: e -> Maybe a -> Either e a
maybeToRight e Nothing = Left e
maybeToRight _ (Just a) = Right a

duplicates :: Eq a => [a] -> [a]
duplicates xs = let (_, dups, _) = aux ([], [], xs) in dups
 where
  aux :: Eq a => ([a], [a], [a]) -> ([a], [a], [a])
  aux (visited, dups, []) = (visited, dups, [])
  aux (visited, dups, (x:xs)) | x `elem` visited = aux (visited, x:dups, xs)
                              | otherwise = aux (x:visited, dups, xs)

-- An infinite list of strings for names:
-- a,b,c,...,a2,b2,c2,...,aN,bN,cN
names :: [String]
names = do
  number <- nums
  letter <- ['a'..'z']
  return (letter:show number)
 where
  nums :: [Int]
  nums = [1..]

-- Versions of `Control.Arrow`'s (***) where one arrow is functorial
(^**) :: Functor f => (a -> f b) -> (a' -> b') -> (a, a') -> f (b, b')
(f ^** g) (a, a') = (,g a') <$> f a

(**^) :: Functor f => (a -> b) -> (a' -> f b') -> (a, a') -> f (b, b')
(f **^ g) (a, a') = (f a,) <$> g a'

infixr 3 **^
infixr 3 ^**
