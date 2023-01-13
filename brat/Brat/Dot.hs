module Brat.Dot where

import Brat.Graph
import Brat.Syntax.Common (PortName, OutPort(..), InPort(..))
import Brat.Syntax.Value

import qualified Data.Map as M

labelType :: Either SValue Value -> (PortName, PortName) -> String
labelType (Left _) _ = ""
labelType (Right vty) (p, q) = unwords ["[label ="
                                       ,show (unwords ["[", show p, "--(" ++ show vty ++ ")->", show q, "]"])
                                       ,"]"]

mkEdge :: Wire -> String
mkEdge (Ex src p, ty, In tgt q) = unwords [show (show src), "->", show (show tgt), labelType ty (show p,show q)]

dot :: Graph -> String
dot g
  = let ((ns, es), subs) = boxSubgraphs g
        subs' = (\(lbl, s) -> ("subgraph cluster_" ++ lbl) ++ subGraph lbl s) <$> subs
        -- Note: `show . show` adds an extra set of quotes so
        -- that Dot will parse the name as a single string
        -- even if it contains spaces
    in  unlines ("digraph {":subs' ++ (show . show <$> M.keys ns) ++ (mkEdge <$> es) ++ ["}"])
 where
  subGraph :: String -> Graph -> String
  subGraph lbl (ns, es) = unlines ("{":("label="++lbl):(show . show <$> M.keys ns) ++ (mkEdge <$> es) ++ ["}"])

