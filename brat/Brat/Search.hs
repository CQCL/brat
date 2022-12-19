module Brat.Search (vsearch, csearch) where

import Data.List (transpose)

import Brat.FC
import Brat.Syntax.Core
import Brat.Syntax.Common
import Brat.UserName

vec :: FC -> [WC (Term Chk Noun)] -> Term Chk Noun
vec fc [] = Con (plain "nil") (WC fc Empty)
vec fc (x:xs) = Con (plain "cons") (WC fc (x :|: WC fc (vec fc xs)))

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
                                       [[vec fc (WC fc <$> list)]]
tokenValues fc (Product s t)
  = zipWith (\a b -> vec fc [(WC fc a), (WC fc b)]) (cycle $ tokenValues fc s) (cycle $ tokenValues fc t)
tokenValues fc (Vector ty (Simple (Num n))) = vec fc <$> (replicate n . WC fc <$> tokenValues fc ty)
tokenValues _ (Vector _ _) = [] -- not enough info
tokenValues fc (K (R ss) (R ts)) =
  let lhs = WC fc (binders ss)
      rhss = tokenRow ts
  in [ Th (WC fc (lhs :\: (WC fc rhs))) | rhs <- rhss ]
 where
  tokenRow :: [(p, SType)] -> [Term Chk Noun]
  tokenRow r = foldr1 comma <$> tokenRows r

  tokenRows :: [(p, SType)] -> [[Term Chk Noun]]
  tokenRows [] = [[]]
  tokenRows ((_, sty):tys) = do
    tm <- tokenSType sty
    rest <- tokenRows tys
    [(tm:rest)]

  tokenSType :: SType -> [Term Chk Noun]
  tokenSType (Q _) = []
  tokenSType Bit = tokenValues fc (SimpleTy Boolean)
  tokenSType (Of (Q _) _) = []
  tokenSType (Of sty (Simple (Num n))) = do
    sty <- tokenSType sty
    [vec fc (WC fc <$> replicate n sty)]
  tokenSType (Of _ _) = []
  tokenSType (Rho (R row)) = tokenRow row

  comma :: Term Chk Noun -> Term Chk Noun -> Term Chk Noun
  comma a b = WC fc a :|: WC fc b

tokenValues fc (Option ty) = (:) (Con (plain "none") (WC fc Empty)) $ do
  val <- tokenValues fc ty
  [Con (plain "some") (WC fc val)]
tokenValues _ _ = []

tokenFuncs :: FC -> CType -> [Term Chk UVerb]
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
 where
  binder = APat . Bind . (:[])

vsearch :: FC -> VType -> [Term Chk Noun]
vsearch fc = take 5 . tokenValues fc

csearch :: FC -> CType -> [Term Chk UVerb]
csearch fc = take 5 . tokenFuncs fc
