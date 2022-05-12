{-# LANGUAGE ScopedTypeVariables, UndecidableInstances #-}

module Brat.Graph where

import Brat.Naming
import Brat.Syntax.Common

import Data.Functor
import Data.List ((\\))
import qualified Data.Graph as G
import Data.Maybe (fromJust)

data Node' tm
  = BratNode Name Thing [Input' tm] [Output' tm]
  | KernelNode Name Thing [(Port, SType' tm)] [(Port, SType' tm)]

nodeName :: Node' tm -> Name
nodeName (BratNode nm _ _ _) = nm
nodeName (KernelNode nm _ _ _) = nm

nodeThing :: Node' tm -> Thing
nodeThing (BratNode _ t _ _) = t
nodeThing (KernelNode _ t _ _) = t

deriving instance Show (tm Chk Noun) => Show (Node' tm)
deriving instance Eq (tm Chk Noun) => Eq (Node' tm)

data Thing
  = Prim String  -- Something in the env
  | Const SimpleTerm
  | Eval Src     -- Something on a wire
  | Name :>>: Name -- Graph in a box
  | Source       -- For building..
  | Target       -- ..boxes
  | Id           -- Identity node for convenient wiring
  | Hypo         -- Hypothesis for type checking
  | Combo Src Src
  | Constructor ConsType
  deriving (Eq, Show)

data ConsType = CCons | CSome | CVec | CList | CPair | CDoub | CSucc
 deriving (Eq, Show)

type Graph' tm = ([Node' tm], [Wire' tm])
{-
newtype BGraph' tm nl el = BG ([Node tm], [Wire tm])
type BGraph tm = BGraph' tm String String

deriving instance Eq (tm Chk Noun) => Eq (BGraph tm)
deriving instance Show (tm Chk Noun) => Show (BGraph tm)
-}
instance {-# OVERLAPPING #-} Show (tm Chk Noun) => Show (Graph' tm) where
  show (ns, ws) = unlines (("Nodes:":(show <$> ns)) ++ ("":"Wires:":(show <$> ws)))

type Wire' tm = (Src, Either (SType' tm) (VType' tm), Tgt)

type Src = (Name, Port)
type Tgt = (Name, Port)

type Input' tm = (Port, VType' tm)
type Output' tm = (Port, VType' tm)

toGraph :: Graph' tm -> (G.Graph, G.Vertex -> (Node' tm, Name, [Name]), Name -> Maybe G.Vertex)
toGraph (ns, ws) = G.graphFromEdges adj
 where
  adj = [ (n
          ,nodeName n
          ,[ tgt | ((src,_), _, (tgt, _)) <- ws, src == nodeName n ]
          )
        | n <- ns]

wiresFrom :: Name -> Graph' tm -> [Wire' tm]
wiresFrom src (_, ws) = [ w | w@((a, _), _, (_, _)) <- ws, a == src ]

lookupNode :: Name -> Graph' tm -> Maybe (Node' tm)
lookupNode name (ns, _) = case [ node | node <- ns, nodeName node == name ] of
                            [x] -> Just x
                            _ -> Nothing

wireStart :: Wire' tm -> Name
wireStart ((x, _), _, _) = x

wireEnd :: Wire' tm -> Name
wireEnd (_, _, (x, _)) = x

boxSubgraphs :: forall tm. Eq (tm Chk Noun)
             => Graph' tm
             -> (Graph' tm, [(String, Graph' tm)])
boxSubgraphs g@(ns,ws) = let subs = fromJust subGraphs
                             (subNodes, subWires) = mconcat $ snd <$> subs
                         in  ((ns \\ subNodes, ws \\ subWires), subs)
 where
  boxes :: [Node' tm] -> [(String, (Name, Name))]
  boxes [] = []
  boxes (n:ns) | (src :>>: tgt) <- nodeThing n = (show (nodeName n), (src,tgt)) : boxes ns
               | otherwise = boxes ns

  subGraphs :: Maybe [(String, Graph' tm)]
  subGraphs = traverse (\(lbl, x) -> (lbl,) <$> boxInsides x) (boxes ns)

  boxInsides :: (Name, Name) -> Maybe (Graph' tm)
  boxInsides (srcId, tgtId) = do
    node  <- lookupNode srcId g
    let wires = wiresFrom srcId g
    case wires of
      [w] | wireEnd w == tgtId -> lookupNode tgtId g <&> \n -> ([n,node], wires)
      _ -> mconcat <$> traverse boxInsides ((\w -> (wireEnd w, tgtId)) <$> wires)

