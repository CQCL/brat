--module Brat.Compile.Simple (simplify, test) where
module Brat.Compile.Simple (removeNode, simplify) where

-- Simplify graph somewhat

import Brat.Graph
import Brat.Naming
import Brat.Syntax.Common (OutPort(..), InPort(..))

import qualified Data.Map as M

simplify :: Graph -> Graph
simplify = removeRedundant

removeNode :: Name -> Graph -> Graph
removeNode n (nodes, wires) = (M.delete n nodes, filter (not . connected) wires)
 where
  connected :: Wire -> Bool
  connected (Ex a _, _, In b _) = a == n || b == n

removeRedundant :: Graph -> Graph
removeRedundant g@(nodes, _)
  = foldr removeNode g (M.keys (M.filter (redundant . nodeThing) nodes))
 where
  redundant :: Thing -> Bool
  redundant Id = True
  redundant Hypo = True
  redundant _ = False
