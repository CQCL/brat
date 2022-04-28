module Brat.Search (vsearch, csearch) where

import Data.List (transpose)

import Brat.FC
import Brat.Syntax.Core
import Brat.Syntax.Common

-- Easiest answers
tokenValues :: FC -> VType -> [Term Chk Noun]
tokenValues fc (C cty) = Th . WC fc <$> tokenFuncs fc cty
tokenValues _  (SimpleTy Natural) = Simple . Num <$> [0..]
tokenValues _  (SimpleTy IntTy) = Simple . Num <$> [0..]
tokenValues _  (SimpleTy Boolean) = [Simple (Bool True), Simple (Bool False)]
tokenValues _  (SimpleTy FloatTy) = Simple . Float <$> [0.0..]
tokenValues _  (SimpleTy TextType) = Simple . Text <$> ("":((:[])<$>['A'..]))
tokenValues _  (SimpleTy Star) = []
tokenValues fc (List ty) = concat $ do tm <- tokenValues fc ty
                                       list <- iterate (tm:) []
                                       [[Vec (WC fc <$> list)]]
tokenValues fc (Product s t)
  = zipWith (\a b -> Vec [(WC fc a), (WC fc b)]) (cycle $ tokenValues fc s) (cycle $ tokenValues fc t)
tokenValues fc (Vector ty (Simple (Num n))) = Vec <$> (replicate n . WC fc <$> tokenValues fc ty)
tokenValues _ (Vector _ _) = [] -- not enough info
tokenValues fc (K _ _) = []
 where
  aux :: SType -> [Term Chk Noun]
  aux (Q _) = []
  aux Bit = tokenValues fc (SimpleTy Boolean)
  aux (Of (Q _) _) = []
  aux (Of sty (Simple (Num n))) = do
    sty <- aux sty
    [Vec (WC fc <$> replicate n sty)]
  aux (Of _ _) = []
  aux (Rho _) = undefined
tokenValues fc (Option ty) = (:) (Pattern (WC fc PNone)) $ do
  val <- tokenValues fc ty
  [Pattern (WC fc (PSome (WC fc val)))]
tokenValues _ _ = []

tokenFuncs :: FC -> CType -> [Term Chk Verb]
tokenFuncs fc (ss :-> ts)
  = case ss of
      [] -> []
      _  -> do
        let lhs = binders ss
        outs <- outputs ts
        [WC fc lhs :\: WC fc outs]
 where
  outputs :: [InOut] -> [Term Chk Noun]
  outputs ts = do outs <- transpose $ tokenValues fc . snd <$> ts
                  [(foldr1 (\ a b -> (WC fc a :|: WC fc b)) outs)]

  binders :: [a] -> Abstractor
  binders xs = foldr1 (:||:) $ zipWith const (binder <$> ['a'..]) xs

  binder = Bind . (:[])

vsearch :: FC -> VType -> [Term Chk Noun]
vsearch fc = take 5 . tokenValues fc

csearch :: FC -> CType -> [Term Chk Verb]
csearch fc = take 5 . tokenFuncs fc
