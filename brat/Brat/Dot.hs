module Brat.Dot where

import Brat.Graph
import Brat.Syntax.Common

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

showType :: Show (tm Chk Noun) => Either (SType tm) (VType' tm) -> String
showType (Left sty) = ""
showType (Right vty) = show (show vty)

mkEdge :: Show (tm Chk Noun) => Wire' tm -> String
mkEdge ((src,_), ty, (tgt,_)) = unwords [show (show src), "->", show (show tgt), "[label =", showType ty, "]"]

dot :: Show (tm Chk Noun) => Graph' tm -> String
dot (ns, es) = unlines ("digraph {":(nodeLabel <$> ns) ++ (mkEdge <$> es) ++ ["}"])
