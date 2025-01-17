module Brat.FC where

data Pos = Pos { line :: Int
               , col  :: Int
               } deriving Eq

instance Show Pos where
  show (Pos { .. }) = show line ++ ":" ++ show col


instance Ord Pos where
  compare (Pos l c) (Pos l' c') | l == l' = compare c c'
                                | otherwise = compare l l'

data FC = FC { start :: Pos
             , end   :: Pos
             } deriving (Eq, Show, Ord)

inside :: Pos -> FC -> Bool
inside pos (FC start end) = (pos >= start) && (pos <= end)

data WC a = WC FC a deriving (Foldable, Functor, Traversable, Ord)
instance Show a => Show (WC a) where
  show (WC _ a) = show a

instance Eq a => Eq (WC a) where
  a == b = unWC a == unWC b

unWC :: WC a -> a
unWC (WC _ a) = a

fcOf :: WC a -> FC
fcOf (WC fc _) = fc

-- TODO: Remove this
dummyFC :: a -> WC a
dummyFC = WC (FC (Pos 0 0) (Pos 0 0))

spanFC :: FC -> FC -> FC
spanFC afc bfc = FC (start afc) (end bfc)

spanFCOf :: WC a -> WC b -> FC
spanFCOf (WC afc _) (WC bfc _) = spanFC afc bfc
