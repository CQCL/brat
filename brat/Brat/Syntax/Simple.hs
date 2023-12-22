module Brat.Syntax.Simple (SimpleTerm(..)
                          ) where

data SimpleTerm
  = Num Int
  | Text String
  | Float Double
  | Unit
  deriving Eq

instance Show SimpleTerm where
  show (Num i) = show i
  show (Text txt) = show txt
  show (Float f) = show f
  show Unit = "[]"
