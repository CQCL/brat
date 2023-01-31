module Brat.UserName where

import Data.List (intercalate)

type Prefix = [String]

data UserName
  = PrefixName Prefix String
  deriving (Eq, Ord)

instance Show UserName where
  show (PrefixName ps file) = intercalate "." (ps ++ [file])

plain :: String -> UserName
plain n = PrefixName [] n
