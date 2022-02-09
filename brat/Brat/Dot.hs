module Brat.Dot where

import Brat.Graph
import Brat.Syntax.Common

import qualified Data.Graph as Graph

{-
instance Graph (BGraph' tm) where
  empty = BG ([], [])
  isEmpty (BG (ns, _)) = null ns
  match n (BG (ns, es)) = Just ([ src | (src, ty, tgt) <- es, tgt == n ]
                               ,n
                               ,[ tgt | (src, ty, tgt) <- es, src == n ])
  mkGraph lns ens = BG (fst <$> lns) (fst <$> ens)
  labNodes (BG (ns, _)) = (\n@(BratNode nm _ _ _) -> (n, show nm)) <$> ns

-}

nodeLabel :: Node' tm -> String
nodeLabel (BratNode nm _ _ _) = show $ show nm
nodeLabel (KernelNode nm _ _ _) = show $ show nm

labelType :: Show (tm Chk Noun) => Either (SType tm) (VType' tm) -> (Port, Port) -> String
labelType (Left sty) _ = ""
labelType (Right vty) (p, q) = unwords ["[label ="
                                       ,show (unwords ["[", p, "--(" ++ show vty ++ ")->", q, "]"])
                                       ,"]"]

mkEdge :: Show (tm Chk Noun) => Wire' tm -> String
mkEdge ((src,p), ty, (tgt,q)) = unwords [show (show src), "->", show (show tgt), labelType ty (p,q)]

dot :: (Eq (tm Chk Noun), Show (tm Chk Noun)) => Graph' tm -> String
dot g
  = let ((ns, es), subs) = boxSubgraphs g
        subs' = (\(lbl, s) -> ("subgraph cluster_" ++ lbl) ++ subGraph lbl s) <$> subs
    in  unlines ("digraph {":subs' ++ (nodeLabel <$> ns) ++ (mkEdge <$> es) ++ ["}"])
 where
  subGraph :: Show (tm Chk Noun) => String -> Graph' tm -> String
  subGraph lbl (ns, es) = unlines ("{":("label="++lbl):(nodeLabel <$> ns) ++ (mkEdge <$> es) ++ ["}"])

