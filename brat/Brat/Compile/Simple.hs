--module Brat.Compile.Simple (simplify, test) where
module Brat.Compile.Simple (simplify) where

-- Simplify graph somewhat

import Brat.Graph
import Brat.Naming
import Brat.Checker

import Debug.Trace

simplify :: Graph -> Graph
simplify = removeRedundant . removeCombo

removeNode :: Node -> Graph -> Graph
removeNode n (nodes, wires) = (filter (not . eq n) nodes, filter connected wires)
 where
  eq :: Node -> Node -> Bool
  eq n n' = (nodeName n == nodeName n')

  connected :: Wire -> Bool
  connected ((a,_), _, (b,_)) = a == nodeName n || b == nodeName n
                      
removeRedundant :: Graph -> Graph
removeRedundant g@(nodes, _) = foldr removeNode g (filter (redundant . nodeThing . traceShowId) nodes)
 where
  redundant :: Thing -> Bool
  redundant Id = True
  redundant Hypo = True
  redundant _ = False

uncombo :: Node -> Graph -> Graph
uncombo n g | Combo l r <- nodeThing n, _ <- nodeName n
 = removeNode n $ rewire (nodeName n) r $ rewire (nodeName n) l g

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
removeCombo g@(nodes,_) = foldr (uncombo . traceShowId) g (filter isCombo nodes)
 where
  isCombo :: Node -> Bool
  isCombo n | Combo _ _ <- nodeThing n = True
            | otherwise = False
