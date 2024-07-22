module Brat.FC where

data Pos = Pos { line :: Int
               , col  :: Int
               } deriving (Eq, Show)

instance Ord Pos where
  compare (Pos l c) (Pos l' c') | l == l' = compare c c'
                                | otherwise = compare l l'

data FC = FC { start :: Pos
             , end   :: Pos
             } deriving (Eq, Show)

inside :: Pos -> FC -> Bool
inside pos (FC start end) = (pos >= start) && (pos <= end)
