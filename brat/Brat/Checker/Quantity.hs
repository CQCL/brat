module Brat.Checker.Quantity where

data Quantity = None | One | Tons deriving Show

qpred :: Quantity -> Maybe Quantity
qpred None = Nothing
qpred One  = Just None
qpred Tons = Just Tons
