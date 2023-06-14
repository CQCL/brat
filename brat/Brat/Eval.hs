module Brat.Eval (apply, Eval(..)) where

import Brat.Syntax.Value
import Brat.Syntax.Common
import Util
import Bwd

import Control.Monad (foldM)


class Eval t where
  type ValOf t
  eval :: Monad m
       => (End -> m (Maybe (Value {- 0 -}))) -- A way to fetch Pars from the store
       -> Bwd {- length: n -} (Value {- 0 -}) -- Context
       -> t {- n -}
       -> m (ValOf t {- 0 -}) -- Inx-closed

instance Eval VVar where
  type ValOf VVar = Maybe Value
  eval g l (VPar e) = g e >>= \case
    Nothing -> pure Nothing
    -- if the End is defined, then evaluate again; it might be another End!
    Just v -> Just <$> eval g l v -- eval g l (v :: Value) -> Value, not Maybe
  eval _ l (VInx i) = pure $ Just (l !< i)
  eval _ _ (VLvl _ _) = pure Nothing

instance Eval Value where
  type ValOf Value = Value
  eval g l (VNum n) = VNum <$> eval g l n
  eval g l (VCon c vs) = VCon c <$> traverse (eval g l) vs
  eval g l (VApp v ss) = do
    ss <- traverse (eval g l) ss
    eval g l v >>= \case
      Nothing -> pure $ VApp v ss
      Just v  -> foldM (apply g) v ss
   where
  eval _ l (VLam ctx v) = pure $ VLam (l <> ctx) v
  eval _ l (VFun m ctx cty) = pure $ VFun m (l <> ctx) cty

apply :: Monad m
      => (End -> m (Maybe (Value {- 0 -})))
      -> Value {- 0 -} -> Value {- 0 -} -> m (Value {- 0 -})
apply g (VLam ctx v) a = eval g (ctx :< a) v
apply _ (VApp v ss) a = pure $ VApp v (ss :< a)
apply _ _ _ = error "apply misused"

instance Eval NumValue where
  type ValOf NumValue = NumValue
  eval g l (NumValue up grow) = nPlus up <$> eval g l grow

instance Eval Fun00 where
  type ValOf Fun00 = NumValue
  eval _ _ Constant0 = pure (nConstant 0)
  eval g l (StrictMonoFun sm) = eval g l sm

instance Eval StrictMono where
  type ValOf StrictMono = NumValue
  eval g l (StrictMono pow mono) = n2PowTimes pow <$> eval g l mono

instance Eval Monotone where
  type ValOf Monotone = NumValue
  eval g l (Linear v) = eval g l v >>= \case
    Just (VNum v) -> eval g l v
    Just (VApp var@(VLvl _ Nat) B0) -> pure $ nVar var
    Nothing -> pure $ nVar v
    _ -> error "Evaluating a NumValue went wrong"
  eval g l (Full sm) = nFull <$> eval g l sm

instance (Eval s, Eval t) => Eval (Either s t) where
  type ValOf (Either s t) = Either (ValOf s) (ValOf t)
  eval g l (Left s) = Left <$> eval g l s
  eval g l (Right t) = Right <$> eval g l t

instance Eval TypeKind where
  type ValOf TypeKind = TypeKind
  eval _ _ = pure

instance Eval v => Eval (SType' v) where
  type ValOf (SType' v) = SType' (ValOf v)
  eval g l (Rho (R row)) = Rho . R <$> traverse (id **^ eval g l) row
  eval g l (Of sty n) = Of <$> eval g l sty <*> eval g l n
  eval _ _ Bit = pure Bit
  eval _ _ (Q q) = pure (Q q)
