module Data.Bracket where

data BracketType = Paren | Bracket | Brace deriving (Eq, Ord)

showOpen :: BracketType -> String
showOpen Paren = "("
showOpen Bracket = "["
showOpen Brace = "{"

showClose :: BracketType -> String
showClose Paren = ")"
showClose Bracket = "]"
showClose Brace = "}"
