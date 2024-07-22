module Brat.Thin where

data Thin = Keep | Drop deriving (Eq, Show)

type Thinning = [Thin]

type Selection = Int -> Thinning

fromNat :: Int -> Int -> Thinning
fromNat size n | n < 0 = error "fromNat: don't"
               | n == 0 = Keep : replicate (size - 1) Drop
               | otherwise = Drop : fromNat (size - 1) (n - 1)

fromNatFrom :: Int -> Int -> Thinning
fromNatFrom size n | n < 0 = error "fromNat: don't"
                   | n == 0 = replicate size Keep
                   | otherwise = Drop : fromNatFrom (size - 1) (n - 1)

union :: Thinning -> Thinning -> Thinning
union th ph | length th /= length ph = error "bad union"
            | otherwise = aux th ph
 where
  aux (Keep:th) (_:ph) = Keep : aux th ph
  aux (_:th) (Keep:ph) = Keep : aux th ph
  aux (_:th) (_:ph) = Drop : aux th ph
  aux [] ph = ph
  aux th [] = th

zeros :: Int -> Thinning
zeros bigEnd = replicate bigEnd Drop

zerosInf :: Thinning
zerosInf = repeat Drop

sep :: [a] -> Thinning -> ([a], [a])
sep (x:xs) (Keep:th) = ([], [x]) <> sep xs th
sep (x:xs) (Drop:th) = ([x], []) <> sep xs th
sep _ [] = error "Thinning is bigger than list"
sep [] _ = error "Thinning is smaller than list"

-- the opposite of `sep`
riffle :: Thinning -> ([a], [a]) -> [a]
riffle [] ([], []) = []
riffle (Keep:th) (ds, (k:ks)) = k : riffle th (ds, ks)
riffle (Drop:th) ((d:ds), ks) = d : riffle th (ds, ks)
riffle [] _ = error "Riffle: thinning is smaller than list"
riffle _ _ = error "Riffle: thinning is bigger than list"

oddsInf :: Thinning
oddsInf = Drop : Keep : oddsInf

odds :: Int -> Thinning
odds n = take n oddsInf

evensInf :: Thinning
evensInf = Keep : Drop : evensInf

evens :: Int -> Thinning
evens n = take n evensInf
