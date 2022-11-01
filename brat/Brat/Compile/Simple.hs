--module Brat.Compile.Simple (simplify, test) where
module Brat.Compile.Simple (removeNode, simplify) where

-- Simplify graph somewhat

import Brat.Graph
import Brat.Naming
import Brat.Syntax.Common (End, Port(..))

import qualified Data.Map as M

simplify :: Graph -> Graph
simplify = removeRedundant . removeCombo

removeNode :: Name -> Graph -> Graph
removeNode n (nodes, wires) = (M.delete n nodes, filter (not . connected) wires)
 where
  connected :: Wire -> Bool
  connected ((a,_), _, (b,_)) = a == n || b == n
                      
removeRedundant :: Graph -> Graph
removeRedundant g@(nodes, _)
  = foldr removeNode g (M.keys (M.filter (redundant . nodeThing) nodes))
 where
  redundant :: Thing -> Bool
  redundant Id = True
  redundant Hypo = True
  redundant _ = False

uncombo :: (Name, Node) -> Graph -> Graph
uncombo (name, node) g@(_,edges)
  | Combo _ <- nodeThing node
  = let outedges = [tgt | ((n, Ex _) ,_, tgt) <- edges, n == name]
    in removeNode name $ foldr (\tgt g -> rewire name tgt g) g $ outedges
  | otherwise = g

rewire :: Name -> End -> Graph -> Graph
rewire old new (nodes, wires) = (nodes, newWires wires)
 where
  newWires :: [Wire] -> [Wire]
  newWires [] = []
  -- Assuming no cycles
  newWires (w@((src, In p), ty, (tgt, Ex q)):ws)
    | src == old = (new,ty,(tgt, In q)) : newWires ws
    | old == tgt = ((src, Ex p),ty,new) : newWires ws
    | otherwise = w : newWires ws
  newWires (w:_) = error $ "Ex -> In Invariant violated by this wire: " ++ show w

removeCombo :: Graph -> Graph
removeCombo g@(nodes,_) = foldr uncombo g $ M.assocs nodes
