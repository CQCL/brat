module Brat.Naming where

import Data.List (intercalate)
import Data.Kind (Type)

type Namespace = (Name, Int)

newtype Name = MkName [(String, Int)] deriving Eq

instance Ord Name where
  -- I don't think it matters at all?
  compare n@(MkName ((x, i):xs)) m@(MkName ((y, j):ys))
    | n == m = EQ
    | x == y = compare i j
    | otherwise = compare x y

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
