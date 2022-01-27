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

class Naming (m :: Type -> Type) where
  fresh :: String -> m Name

root :: Namespace
root = (MkName [], 0)

instance Show Name where
  show (MkName x) = intercalate "/"  $ fmap (\(str, n) ->
                                                case n of
                                                  0 -> str
                                                  _ -> str ++ "_" ++ show n) (reverse x)
