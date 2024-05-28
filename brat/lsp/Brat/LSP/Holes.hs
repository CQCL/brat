module Brat.LSP.Holes where

import Brat.Checker.Types (TypedHole(..), HoleData(..))
import Brat.FC (FC)

holeInfo :: TypedHole -> (FC, String)
holeInfo h@(TypedHole _ HoleData { .. }) = (fc,
                                            unlines (show h : maybe [] (delim:) suggestions)
                                           )
 where
  delim = replicate (length (show h)) '-'
