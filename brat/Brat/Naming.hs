module Brat.Naming where

import Data.List (intercalate)

type Namespace = (Name, Int)

newtype Name = MkName [(String, Int)] deriving Eq

instance Ord Name where
  compare (MkName a) (MkName b) = aux a b
   where
    aux n m | n == m = EQ
    aux ((x, i):xs) ((y, j):ys)
     | x == y = compare i j <> compare xs ys
     | otherwise = compare x y
    aux [] _ = LT
    aux _ [] = GT

fresh :: String -> Namespace -> (Name, Namespace)
fresh str (MkName nm, i) = (MkName ((str, i):nm), (MkName nm, i + 1))

split :: String -> Namespace -> (Namespace, Namespace)
split str (MkName nm, i) = ((MkName ((str,i):nm), 0), (MkName nm, i + 1))

root :: Namespace
root = (MkName [], 0)

instance Show Name where
  show (MkName x) = intercalate "_"  $ fmap (\(str, n) ->
                                                case n of
                                                  0 -> str
                                                  _ -> str ++ "_" ++ show n) (reverse x)
