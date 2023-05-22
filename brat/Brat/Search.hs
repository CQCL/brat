module Brat.Search (vsearch) where

import Brat.FC
import Brat.Syntax.Core
import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.Syntax.Simple
import Brat.UserName
import Bwd


vec :: FC -> [WC (Term Chk Noun)] -> Term Chk Noun
vec fc [] = Con (plain "nil") (WC fc Empty)
vec fc (x:xs) = Con (plain "cons") (WC fc (x :|: WC fc (vec fc xs)))

binders :: Int -> Abstractor
binders n = foldr1 (:||:) $ take n (APat . Bind . (:[]) <$> ['a'..])

tokenRow :: FC -> (a -> [Term Chk Noun]) -> TypeRow a -> [Term Chk Noun]
tokenRow fc f r = foldr1 comma <$> tokenRows r
 where
  comma a b = WC fc a :|: WC fc b

  tokenRows [] = [[]]
  tokenRows (x:xs) = do
    tm <- f (forgetPortName x)
    rest <- tokenRows xs
    [tm:rest]

-- Easiest answers
tokenValues :: FC -> Value -> [Term Chk Noun]
tokenValues _ TNat = Simple . Num <$> [0..]
tokenValues _ TInt = Simple . Num <$> [0..]
tokenValues _ TBool = [Simple (Bool True), Simple (Bool False)]
tokenValues _ TFloat = Simple . Float <$> [0.0..]
tokenValues _ TText = Simple . Text <$> ("":((:[])<$>['A'..]))
tokenValues fc (TOption ty) = (:) (Con (plain "none") (WC fc Empty)) $ do
  val <- tokenValues fc ty
  [Con (plain "some") (WC fc val)]
tokenValues fc (TList ty) = concat $ do
  tm <- tokenValues fc ty
  list <- iterate (tm:) []
  [[vec fc (WC fc <$> list)]]
tokenValues fc (TVec ty (VNum (NumValue n Constant0))) = do
  tm <- tokenValues fc ty
  [vec fc (replicate n $ WC fc tm)]
tokenValues _ (TVec _ _) = [] -- not enough info
tokenValues fc (VFun Braty B0 (ss :-> ts)) =
  [ Th (WC fc (WC fc abs :\: WC fc t)) | t <- rhs ]
 where
  abs = binders (length ss)
  rhs = tokenRow fc (\case Left _ -> []
                           Right v -> tokenValues fc v) (toTypeRow ts)
tokenValues fc (VFun Kerny B0 (ss :-> ts)) =
  [ Th (WC fc (WC fc abs :\: WC fc t)) | t <- rhs ]
 where
  abs = binders (length ss)
  rhs = tokenRow fc tokenSType (toTypeRow ts)

  tokenSType :: SValue -> [Term Chk Noun]
  tokenSType (Q _) = []
  tokenSType Bit = tokenValues fc TBool
  tokenSType (Of (Q _) _) = []
  tokenSType (Of sty (VNum (NumValue n Constant0))) = do
    tm <- tokenSType sty
    [vec fc (replicate n $ WC fc tm)]
  tokenSType (Of _ _) = []
  tokenSType (Rho (R row)) = tokenRow fc tokenSType (toTypeRow row)
tokenValues _ _ = []

vsearch :: FC -> Value -> [Term Chk Noun]
vsearch fc = take 5 . tokenValues fc
