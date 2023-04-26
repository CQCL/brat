module Brat.Syntax.Simple (SimpleTerm(..)
                          ) where

data SimpleTerm
  = Num Int
  | Bool Bool
  | Text String
  | Float Double
  | Unit
  deriving Eq

instance Show SimpleTerm where
  show (Num i) = show i
  show (Bool True) = "true"
  show (Bool False) = "false"
  show (Text txt) = show txt
  show (Float f) = show f
  show Unit = "[]"
