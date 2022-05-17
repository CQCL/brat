--module Brat.Compile.Simple (simplify, test) where
module Brat.Compile.Simple (removeNode, simplify) where

-- Simplify graph somewhat

import Brat.Graph
import Brat.Naming
import Brat.Checker

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
uncombo (name, node) g
  | Combo l r <- nodeThing node
  = removeNode name $ rewire name r $ rewire name l g
  | otherwise = g

rewire :: Name -> Src -> Graph -> Graph
rewire old new (nodes, wires) = (nodes, newWires wires)
 where
  newWires :: [Wire' tm] -> [Wire' tm]
  newWires [] = []
  -- Assuming no cycles
  newWires (w@((src, p), ty, (tgt, q)):ws)
    | src == old = (new,ty,(tgt, q)) : newWires ws
    | old == tgt = ((src, p),ty,new) : newWires ws
    | otherwise = w : newWires ws

removeCombo :: Graph -> Graph
removeCombo g@(nodes,_)
  = foldr uncombo g (M.assocs (M.filter isCombo nodes))
 where
  isCombo :: Node -> Bool
  isCombo n | Combo _ _ <- nodeThing n = True
            | otherwise = False
