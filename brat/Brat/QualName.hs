module Brat.QualName where

import Data.List (intercalate)

type Prefix = [String]

data QualName = PrefixName Prefix String
  deriving (Eq, Ord)

instance Show QualName where
  show (PrefixName ps file) = intercalate "." (ps ++ [file])

plain :: String -> QualName
plain = PrefixName []
