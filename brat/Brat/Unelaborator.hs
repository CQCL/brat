module Brat.Unelaborator (unelab) where

import Brat.FC (unWC)
import Brat.Syntax.Concrete (Flat(..))
import Brat.Syntax.Common (Dir(..), Kind(..), Diry(..), Kindy(..)
                          ,KindOr, PortName, TypeRowElem(Named), CType'(..), pattern R
                          ,SType', pattern Rho, pattern Q, pattern Bit, pattern Of
                          )
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Raw (Raw(..), RawVType)

import Data.Bifunctor (second)

unelab :: Diry d -> Kindy k -> Term d k -> Flat
unelab _ _ (Simple tm) = FSimple tm
unelab dy ky (Let abs expr body) = FLetIn abs (unelab Syny Nouny <$> expr) (unelab dy ky <$> body)
unelab _ _ (NHole name) = FHole (show name)
unelab _ _ (VHole name) = FHole (show name)
unelab _ _ Empty = FEmpty
unelab dy ky (a :|: b) = FJuxt (unelab dy ky <$> a) (unelab dy ky <$> b)
unelab _ _ Pass = FPass
unelab _ _ (Th thunk) = FThunk (unelab Chky UVerby <$> thunk)
unelab _ _ (TypedTh thunk) = FThunk (unelab Syny KVerby <$> thunk)
unelab _ _ (Force tm) = unelab Syny Nouny (unWC tm)
unelab _ ky (Emb tm) = unelab Syny ky (unWC tm)
unelab dy _ (Forget tm) = unelab dy KVerby (unWC tm)
unelab _ ky (Pull ps tm) = FPull ps (unelab Chky ky <$> tm)
unelab _ _ (Var v) = FVar v
unelab dy ky (Arith op lhs rhs) = FArith op (unelab dy ky <$> lhs) (unelab dy ky <$> rhs)
unelab _ _ (tm ::: outs) = FAnnotation (unelab Chky Nouny <$> tm) (toRawRo outs)
unelab dy ky (top :-: bot) = case ky of
  Nouny -> FInto (unelab Syny Nouny <$> top) (unelab dy UVerby <$> bot)
  _ -> FApp (unelab Syny ky <$> top) (unelab dy UVerby <$> bot)
unelab dy ky (f :$: s) = FApp (unelab dy KVerby <$> f) (unelab Chky ky <$> s)
unelab dy _ (abs :\: bod) = FLambda abs (unelab dy Nouny <$> bod)
unelab _ _ (Con c args) = FCon c (unelab Chky Nouny <$> args)
unelab _ _ (C cty) = FFn $ fmap (\(p, bty) -> Named p (second toRaw bty)) cty
unelab _ _ (K (R ss) (R ts)) = FKernel (toRawKRo ss :-> toRawKRo ts)

-- This is needed for concrete terms which embed a type as a list of `Raw` things
toRaw :: Term d k -> Raw d k
toRaw (Simple tm) = RSimple tm
toRaw (Let abs thing body) = RLet abs (toRaw <$> thing) (toRaw <$> body)
toRaw (NHole name) = RNHole (show name)
toRaw (VHole name) = RVHole (show name)
toRaw Empty = REmpty
toRaw (a :|: b) = (toRaw <$> a) ::|:: (toRaw <$> b)
toRaw Pass = RPass
toRaw (Th th) = RTh $ toRaw <$> th
toRaw (TypedTh th) = RTypedTh $ toRaw <$> th
toRaw (Force tm) = RForce $ toRaw <$> tm
toRaw (Emb tm) = REmb $ toRaw <$> tm
toRaw (Forget tm) = RForget $ toRaw <$> tm
toRaw (Pull ps tm) = RPull ps $ toRaw <$> tm
toRaw (Var v) = RVar v
toRaw (Arith op lhs rhs) = RArith op (toRaw <$> lhs) (toRaw <$> rhs)
toRaw (tm ::: outs) = (toRaw <$> tm) ::::: toRawRo outs
toRaw (top :-: bot) = (toRaw <$> top) ::-:: (toRaw <$> bot)
toRaw (f :$: s) = (toRaw <$> f) ::$:: (toRaw <$> s)
toRaw (abs :\: body) = abs ::\:: (toRaw <$> body)
toRaw (Con c args) = RCon c (toRaw <$> args)
toRaw (C (ss :-> ts)) = RFn (toRawRo ss :-> toRawRo ts)
toRaw (K (R ss) (R ts)) = RKernel (toRawKRo ss :-> toRawKRo ts)

toRawRo :: [(PortName, KindOr (Term Chk Noun))] -> [TypeRowElem (KindOr RawVType)]
toRawRo = fmap (\(p, bty) -> Named p (second toRaw bty))

toRawKRo :: [(PortName, SType' (Term Chk Noun))] -> [(TypeRowElem (SType' (Raw Chk Noun)))]
toRawKRo = fmap (\(p, ty) -> Named p (toRawK ty))
 where
  toRawK :: SType' (Term Chk Noun) -> SType' (Raw Chk Noun)
  toRawK (Q q) = Q q
  toRawK Bit = Bit
  toRawK (Of ty n) = Of (toRawK ty) (toRaw n)
  toRawK (Rho (R row)) = Rho (R (second toRawK <$> row))
