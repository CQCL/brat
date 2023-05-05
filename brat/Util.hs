module Util where

nth :: [a] -> Int -> Maybe a
nth [] _ = Nothing
nth (a:_) 0 = Just a
nth (_:as) n = as `nth` (n - 1)

zip_same_length :: [a] -> [b] -> Maybe [(a,b)]
zip_same_length (x:xs) (y:ys) = ((x,y):) <$> zip_same_length xs ys
zip_same_length [] [] = Just []
zip_same_length _ _ = Nothing

lookupBy :: (a -> Bool) -> (a -> b) -> [a] -> Maybe b
lookupBy _ _ [] = Nothing
lookupBy p f (x:xs) | p x = Just (f x)
                    | otherwise = lookupBy p f xs

maybeToRight :: e -> Maybe a -> Either e a
maybeToRight e Nothing = Left e
maybeToRight _ (Just a) = Right a

duplicatesWith :: Eq b => (a -> b) -> [a] -> [a]
duplicatesWith f xs = let (_, dups, _) = aux ([], [], xs) in dups
 where
  aux (visited, dups, []) = (visited, dups, [])
  aux (visited, dups, (x:xs)) | f x `elem` visited = aux (visited, x:dups, xs)
                              | otherwise = aux (f x:visited, dups, xs)

duplicates :: Eq a => [a] -> [a]
duplicates = duplicatesWith id

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
