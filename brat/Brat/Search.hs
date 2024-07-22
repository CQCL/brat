module Brat.Search (vsearch, csearch) where

import Data.List (transpose,zipWith)

import Brat.Syntax.Core
import Brat.Syntax.Common

-- Easiest answers
tokenValues :: VType -> [Term Chk Noun]
tokenValues (C cty) = Th . Uhh <$> tokenFuncs cty
tokenValues (SimpleTy Natural) = Simple . Num <$> [0..]
tokenValues (SimpleTy IntTy) = Simple . Num <$> [0..]
tokenValues (SimpleTy Boolean) = [Simple (Bool True), Simple (Bool False)]
tokenValues (SimpleTy FloatTy) = Simple . Float <$> [0.0..]
tokenValues (SimpleTy TextType) = Simple . Text <$> ("":((:[])<$>['A'..]))
tokenValues (SimpleTy Star) = []
tokenValues (List ty) = concat $ do tm <- tokenValues ty
                                    list <- iterate (tm:) []
                                    [[Vec (Uhh <$> list)]]
tokenValues (Product s t)
  = zipWith (\a b -> Pair (Uhh a) (Uhh b)) (cycle $ tokenValues s) (cycle $ tokenValues t)
tokenValues (Vector ty (Simple (Num n))) = Vec <$> (replicate n . Uhh <$> tokenValues (SimpleTy Natural))
tokenValues (Vector _ _) = [] -- not enough info
tokenValues (K ss ts) = undefined
 where
  aux :: SType Term -> [Term Chk Noun]
  aux (Q q) = []
  aux Bit = tokenValues (SimpleTy Boolean)
  aux (Of (Q q) n) = []
  aux (Of sty (Simple (Num n))) = do
    sty <- aux sty
    [Vec (Uhh <$> replicate n sty)]
  aux (Of _ _) = []
  aux (Rho _) = undefined
tokenValues (Option ty) = (:) (Pattern (Uhh PNone)) $ do
  val <- tokenValues ty
  [Pattern (Uhh (PSome (Uhh val)))]

tokenFuncs :: CType -> [Term Chk Verb]
tokenFuncs (ss :-> ts)
  = case ss of
      [] -> []
      _  -> do
        let n = length ss
        let lhs = binders (length ss) 0
        outs <- outputs ts
        [lhs :\: Uhh outs]
 where
  binders :: Int -> Int -> Abstractor
  binders 1 n = Bind ((:[]) ['a'..]!!n)
  binders m n = Bind ((:[]) ['a'..]!!n) :||: binders (m - 1) (n + 1)

  outputs :: [InOut] -> [Term Chk Noun]
  outputs ts = do outs <- transpose $ tokenValues . snd <$> ts
                  [(foldr1 (\ a b -> (Uhh a :|: Uhh b)) outs)]

vsearch :: VType -> [Term Chk Noun]
vsearch = take 5 . tokenValues

csearch :: CType -> [Term Chk Verb]
csearch = take 5 . tokenFuncs
