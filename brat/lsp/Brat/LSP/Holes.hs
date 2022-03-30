module Brat.LSP.Holes where

import Data.List (intercalate)

import Brat.Checker (TypedHole(..))
import Brat.FC
import Brat.Naming

holeInfo :: TypedHole -> (FC, String)
holeInfo (NBHole x fc sugg ((), outs))
  = let holeTy = (showHole x (showType False [] (snd <$> outs)))
    in  (fc, unlines (holeTy:(replicate (length holeTy) '-'):sugg))
holeInfo (VBHole x fc (ins, outs))
  = (fc, showHole x (showType False (snd <$> ins) (snd <$> outs)))
holeInfo (NKHole x fc ((), outs))
  = (fc, showHole x (showType True [] (snd <$> outs)))
holeInfo (VKHole x fc (ins, outs))
  = (fc, showHole x (showType True (snd <$> ins) (snd <$> outs)))

showHole :: Name -> String -> String
showHole nm ty = showName nm ++ " :: " ++ ty

showType :: Show a
         => {- isQuantum -}Bool -> [a] -> [a] -> String
showType _ [] outs = showRow outs
showType True ins outs = showRow ins ++ " -o " ++ showRow outs
showType False ins outs = showRow ins ++ " -> " ++ showRow outs

showRow :: Show a => [a] -> String
showRow [] = "()"
showRow [a] = show a
showRow as = intercalate ", " (show <$> as)

showName :: Name -> String
showName (MkName (x:xs)) = show (MkName [x])
