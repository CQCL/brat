{-# LANGUAGE ScopedTypeVariables, UndecidableInstances #-}

module Brat.Graph where

import Brat.Naming
import Brat.Syntax.Common

import qualified Data.Graph as G
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Brat.Syntax.Core (Input, Output, SType, VType)

data Node
  = BratNode Thing [Input] [Output]
  | KernelNode Thing [(PortName, SType)] [(PortName, SType)]
 deriving (Eq, Show)

nodeThing :: Node -> Thing
nodeThing (BratNode t _ _) = t
nodeThing (KernelNode t _ _) = t

data ComboType = Row | Thunk deriving (Eq, Show);

data Thing
  = Prim String  -- Something in the env
  | Const SimpleTerm
  | Eval OutPort   -- Something on a wire
  | Name :>>: Name -- Graph in a box
  | Source       -- For building..
  | Target       -- ..boxes
  | Id           -- Identity node for convenient wiring
  | Hypo         -- Hypothesis for type checking
  | Combo ComboType -- inputs are wired in later
  | Constructor DataNode
  | Selector DataNode
  deriving (Eq, Show)

data DataNode = DCons | DNil | DSome | DNone | DPair | DDoub | DSucc
 deriving (Eq, Show)

type Graph = (M.Map Name Node, [Wire])
emptyGraph :: Graph
emptyGraph = (M.empty, [])

instance {-# OVERLAPPING #-} Show Graph where
  show (ns, ws) = unlines (("Nodes:":(show <$> M.toList ns)) ++ ("":"Wires:":(show <$> ws)))

type Wire = (OutPort, Either SType VType, InPort)

toGraph :: Graph -> (G.Graph, G.Vertex -> (Node, Name, [Name]), Name -> Maybe G.Vertex)
toGraph (ns, ws) = G.graphFromEdges adj
 where
  -- TODO: Reduce the complexity (O(n^2)) of this function
  adj = [ (node
          ,name
          ,[ tgt | (Ex src _, _, In tgt _) <- ws, src == name ]
          )
        | (name, node) <- M.toList ns]

wiresFrom :: Name -> Graph -> [Wire]
wiresFrom src (_, ws) = [ w | w@(Ex a _, _, _) <- ws, a == src ]

lookupNode :: Name -> Graph -> Maybe (Node)
lookupNode name (ns, _) = M.lookup name ns

wireStart :: Wire -> Name
wireStart (Ex x _, _, _) = x

wireEnd :: Wire -> Name
wireEnd (_, _, In x _) = x

boxSubgraphs :: Graph -> (Graph, [(String, Graph)])
boxSubgraphs g@(ns,ws) = let subs = fromJust subGraphs
                             (subNodes, subWires) = mconcat $ snd <$> subs
                         in  ((ns M.\\ subNodes, deleteAll wireEq subWires ws)
                             ,subs)
 where
  wireEq :: Wire -> Wire -> Bool
  wireEq (a0, _, b0) (a1, _, b1) = (a0 == a1) || (b0 == b1)

  elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
  elemBy f a xs = any (f a) xs

  deleteAll :: (a -> a -> Bool) -> [a] -> [a] -> [a]
  deleteAll _ _ [] = []
  deleteAll f as (x:xs) | elemBy f x as = deleteAll f as xs
                        | otherwise = x : deleteAll f as xs

  box :: (Name, Node) -> [(String, (Name, Name))]
  box (nm,n)
    | src :>>: tgt <- nodeThing n = [(show nm, (src,tgt))]
    | otherwise = []

  subGraphs :: Maybe [(String, Graph)]
  subGraphs = traverse (\(lbl, x) -> (lbl,) <$> boxInsides x) (M.toList ns >>= box)

  boxInsides :: (Name, Name) -> Maybe (Graph)
  boxInsides (srcId, tgtId) = do
    let wires = wiresFrom srcId g
    case wires of
      [w] | wireEnd w == tgtId -> do
              src <- lookupNode srcId g
              tgt <- lookupNode tgtId g
              pure (M.fromList [(srcId, src),(tgtId, tgt)], wires)
      _ -> mconcat <$> traverse boxInsides ((\w -> (wireEnd w, tgtId)) <$> wires)

