module Brat.Naming where

import Data.List (intercalate)
import Data.Kind (Type)

type Namespace = (Name, Int)

newtype Name = MkName [(String, Int)] deriving Eq

class Naming (m :: Type -> Type) where
  fresh :: String -> m Name

root :: Namespace
root = (MkName [], 0)

instance Show Name where
  show (MkName x) = intercalate "/"  $ fmap (\(str, n) ->
                                                case n of
                                                  0 -> str
                                                  _ -> str ++ "_" ++ show n) (reverse x)
