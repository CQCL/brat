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

data WC a = WC FC a deriving (Foldable, Functor, Traversable)
instance Show a => Show (WC a) where
  show (WC _ a) = show a

instance Eq a => Eq (WC a) where
  a == b = unWC a == unWC b

unWC :: WC a -> a
unWC (WC _ a) = a

fcOf :: WC a -> FC
fcOf (WC fc _) = fc

