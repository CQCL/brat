{-# LANGUAGE ScopedTypeVariables, UndecidableInstances #-}

module Brat.Graph where

import Brat.Naming
import Brat.Syntax.Common

import Data.List ((\\))
import qualified Data.Graph as G
import qualified Data.Map as M
import Data.Maybe (fromJust)

data Node' tm
  = BratNode Thing [Input' tm] [Output' tm]
  | KernelNode Thing [(Port, SType' tm)] [(Port, SType' tm)]

nodeThing :: Node' tm -> Thing
nodeThing (BratNode t _ _) = t
nodeThing (KernelNode t _ _) = t

deriving instance Show (tm Chk Noun) => Show (Node' tm)
deriving instance Eq (tm Chk Noun) => Eq (Node' tm)

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
  | Constructor ConsType
  deriving (Eq, Show)

data ConsType = CCons | CSome | CVec | CList | CPair | CDoub | CSucc
 deriving (Eq, Show)

type Graph' tm = (M.Map Name (Node' tm), [Wire' tm])
{-
newtype BGraph' tm nl el = BG ([Node tm], [Wire tm])
type BGraph tm = BGraph' tm String String

deriving instance Eq (tm Chk Noun) => Eq (BGraph tm)
deriving instance Show (tm Chk Noun) => Show (BGraph tm)
-}
instance {-# OVERLAPPING #-} Show (tm Chk Noun) => Show (Graph' tm) where
  show (ns, ws) = unlines (("Nodes:":(show <$> M.toList ns)) ++ ("":"Wires:":(show <$> ws)))

type Wire' tm = (Src, Either (SType' tm) (VType' tm), Tgt)

type Src = (Name, Port)
type Tgt = (Name, Port)

type Input' tm = (Port, VType' tm)
type Output' tm = (Port, VType' tm)

toGraph :: Graph' tm -> (G.Graph, G.Vertex -> (Node' tm, Name, [Name]), Name -> Maybe G.Vertex)
toGraph (ns, ws) = G.graphFromEdges adj
 where
  -- TODO: Reduce the complexity (O(n^2)) of this function
  adj = [ (node
          ,name
          ,[ tgt | ((src,_), _, (tgt, _)) <- ws, src == name ]
          )
        | (name, node) <- M.toList ns]

wiresFrom :: Name -> Graph' tm -> [Wire' tm]
wiresFrom src (_, ws) = [ w | w@((a, _), _, (_, _)) <- ws, a == src ]

lookupNode :: Name -> Graph' tm -> Maybe (Node' tm)
lookupNode name (ns, _) = M.lookup name ns

wireStart :: Wire' tm -> Name
wireStart ((x, _), _, _) = x

wireEnd :: Wire' tm -> Name
wireEnd (_, _, (x, _)) = x

boxSubgraphs :: forall tm. Eq (tm Chk Noun)
             => Graph' tm
             -> (Graph' tm, [(String, Graph' tm)])
boxSubgraphs g@(ns,ws) = let subs = fromJust subGraphs
                             (subNodes, subWires) = mconcat $ snd <$> subs
                         in  ((ns M.\\ subNodes, ws \\ subWires), subs)
 where
  box :: (Name, Node' tm) -> [(String, (Name, Name))]
  box (nm,n)
    | src :>>: tgt <- nodeThing n = [(show nm, (src,tgt))]
    | otherwise = []

  subGraphs :: Maybe [(String, Graph' tm)]
  subGraphs = traverse (\(lbl, x) -> (lbl,) <$> boxInsides x) (M.toList ns >>= box)

  boxInsides :: (Name, Name) -> Maybe (Graph' tm)
  boxInsides (srcId, tgtId) = do
    let wires = wiresFrom srcId g
    case wires of
      [w] | wireEnd w == tgtId -> do
              src <- lookupNode srcId g
              tgt <- lookupNode tgtId g
              pure (M.fromList [(srcId, src),(tgtId, tgt)], wires)
      _ -> mconcat <$> traverse boxInsides ((\w -> (wireEnd w, tgtId)) <$> wires)

