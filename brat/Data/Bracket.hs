module Data.Bracket where

data BracketType = Paren | Square | Brace deriving (Eq, Ord)

showOpen :: BracketType -> String
showOpen Paren = "("
showOpen Square = "["
showOpen Brace = "{"

showClose :: BracketType -> String
showClose Paren = ")"
showClose Square = "]"
showClose Brace = "}"
