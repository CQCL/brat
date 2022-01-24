module Util where

lookupBy :: (a -> Bool) -> (a -> b) -> [a] -> Maybe b
lookupBy _ _ [] = Nothing
lookupBy p f (x:xs) | p x = Just (f x)
                    | otherwise = lookupBy p f xs

maybeToRight :: e -> Maybe a -> Either e a
maybeToRight e Nothing = Left e
maybeToRight _ (Just a) = Right a

duplicates :: Eq a => [a] -> [a]
duplicates xs = let (_, dups, []) = aux ([], [], xs) in dups
 where
  aux :: Eq a => ([a], [a], [a]) -> ([a], [a], [a])
  aux (visited, dups, []) = (visited, dups, [])
  aux (visited, dups, (x:xs)) | x `elem` visited = aux (visited, x:dups, xs)
                              | otherwise = aux (x:visited, dups, xs)
