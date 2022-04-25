module Brat.Dot where

import Brat.Graph
import Brat.Syntax.Common

nodeLabel :: Node' tm -> String
nodeLabel (BratNode nm _ _ _) = show $ show nm
nodeLabel (KernelNode nm _ _ _) = show $ show nm

labelType :: Show (tm Chk Noun) => Either (SType' tm) (VType' tm) -> (Port, Port) -> String
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

