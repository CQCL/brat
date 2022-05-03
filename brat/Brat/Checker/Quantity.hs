module Brat.Checker.Quantity where

data Quantity = None | One | Tons

qpred :: Quantity -> Maybe Quantity
qpred None = Nothing
qpred One  = Just None
qpred Tons = Just Tons
