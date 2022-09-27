{-# LANGUAGE ScopedTypeVariables, UndecidableInstances #-}

module Brat.Graph where

import Brat.Naming
import Brat.Syntax.Common

import Data.List ((\\))
import qualified Data.Graph as G
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Brat.Syntax.Core (Input, Output, SType, VType)

data Node
  = BratNode Thing [Input] [Output]
  | KernelNode Thing [(Port, SType)] [(Port, SType)]
 deriving (Eq, Show)

nodeThing :: Node -> Thing
nodeThing (BratNode t _ _) = t
nodeThing (KernelNode t _ _) = t

data ComboType = Row | Thunk deriving (Eq, Show);

data Thing
  = Prim String  -- Something in the env
  | Const SimpleTerm
  | Eval Src     -- Something on a wire
  | Name :>>: Name -- Graph in a box
  | Source       -- For building..
  | Target       -- ..boxes
  | Id           -- Identity node for convenient wiring
  | Hypo         -- Hypothesis for type checking
  | Combo ComboType -- inputs are wired in later
  | Constructor DataNode
  | Selector DataNode
  deriving (Eq, Show)

data DataNode = DCons | DSome | DPair | DDoub | DSucc | DNil
 deriving (Eq, Show)

type Graph = (M.Map Name Node, [Wire])

instance {-# OVERLAPPING #-} Show Graph where
  show (ns, ws) = unlines (("Nodes:":(show <$> M.toList ns)) ++ ("":"Wires:":(show <$> ws)))

type Wire = (Src, Either SType VType, Tgt)

type Src = (Name, Port)
type Tgt = (Name, Port)

toGraph :: Graph -> (G.Graph, G.Vertex -> (Node, Name, [Name]), Name -> Maybe G.Vertex)
toGraph (ns, ws) = G.graphFromEdges adj
 where
  -- TODO: Reduce the complexity (O(n^2)) of this function
  adj = [ (node
          ,name
          ,[ tgt | ((src,_), _, (tgt, _)) <- ws, src == name ]
          )
        | (name, node) <- M.toList ns]

wiresFrom :: Name -> Graph -> [Wire]
wiresFrom src (_, ws) = [ w | w@((a, _), _, (_, _)) <- ws, a == src ]

lookupNode :: Name -> Graph -> Maybe (Node)
lookupNode name (ns, _) = M.lookup name ns

wireStart :: Wire -> Name
wireStart ((x, _), _, _) = x

wireEnd :: Wire -> Name
wireEnd (_, _, (x, _)) = x

boxSubgraphs :: Graph -> (Graph, [(String, Graph)])
boxSubgraphs g@(ns,ws) = let subs = fromJust subGraphs
                             (subNodes, subWires) = mconcat $ snd <$> subs
                         in  ((ns M.\\ subNodes, ws \\ subWires), subs)
 where
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

