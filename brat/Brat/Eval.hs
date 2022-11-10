{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

module Brat.Eval (evalTerm, Value(..)) where

import Brat.Error
import Brat.FC
import Brat.Syntax.Common
import Brat.Syntax.Core

import Control.Monad.Except

data Value
 = VSimple SimpleTerm
-- | ((:|:)  :: Term d k -> Term d k -> Term d k
-- | (Th     :: Term Chk Verb -> Term Chk Noun
-- | (Emb    :: Term Syn k -> Term Chk k
-- | (Pull   :: [Port] -> Term Chk k -> Term Chk k
-- | (Var    :: String -> Term Syn Noun  -- Look up in noun (value) env
-- | ((:$:)  :: Term Syn Noun -> Term Chk Noun -> Term Syn Noun
-- | ((:::)  :: Term Chk k -> [Output] -> Term Syn k
-- | ((:-:)  :: Term Syn k -> Term d Verb -> Term d k
-- | ((:\:)  :: Abstractor -> Term d Noun -> Term d Verb
 | VVec [Value]
 | VCons Value Value
 | VClos [Value] (Term Chk Verb)
 | Value :$ [Elim]
 | VSome Value
 | VNone
 deriving (Eq, Show)

data Elim
 = EApp Value
 | EThin Value
 | ESelect Value
 | EPlus Value
 | ETimes Value
 deriving (Eq, Show)

type Eval = Except Error

class Valuable x where
  eval :: [Value] -> WC x -> Eval Value
  eval' :: [Value] -> x -> Eval Value

instance Valuable (Term Chk k) where
  eval = ceval
  eval' = ceval'

instance Valuable (Term Syn k) where
  eval = seval
  eval' = seval'

addFCToError :: FC -> Eval a -> Eval a
addFCToError fc m = case runExcept m of
                      Right v -> pure v
                      Left (Err _ src msg) -> throwError (Err (Just fc) src msg)

ceval :: [Value] -> WC (Term Chk k) -> Eval Value
ceval g (WC fc tm) = addFCToError fc (ceval' g tm)

ceval' :: [Value] -> Term Chk k -> Eval Value
ceval' _ (Simple tm) = pure $ VSimple tm
-- ceval g ( ((:|:)  :: Term d k -> Term d k -> Term d k
-- ceval g ( (Th     :: Term Chk Verb -> Term Chk Noun
-- ceval g ( (Emb    :: Term Syn k -> Term Chk k
-- ceval g ( (Pull   :: [Port] -> Term Chk k -> Term Chk k
-- ceval g ( (Var    :: String -> Term Syn Noun  -- Look up in noun (value) env
-- ceval g ( ((:-:)  :: Term Syn k -> Term d Verb -> Term d k
ceval' g (Th f) = pure $ VClos g (unWC f)
ceval' g (_ :\: body) = eval g body
ceval' g (Emb tm) = seval g tm
-- eval g (Closure [Value] (Term d k)
ceval' _ tm = throwError $ dumbErr (Unimplemented "ceval" [show tm])

seval :: [Value] -> WC (Term Syn k) -> Eval Value
seval g (WC fc tm) = addFCToError fc (seval' g tm)

seval' :: [Value] -> Term Syn k -> Eval Value
seval' g (tm ::: _) = ceval g tm
seval' g (fun :$: arg) = do
  fun <- seval g fun
  arg <- ceval g arg
  apply fun [EApp arg]
seval' g (_ :\: body) = eval g body
seval' _ tm = throwError $ dumbErr (Unimplemented "seval" [show tm])

pattern VNat n = VSimple (Num n)

apply :: Value -> [Elim] -> Eval Value
apply (VClos g v) (EApp v':es) = eval' (v':g) v >>= flip apply es
apply (VNat m) ((EPlus (VNat n)):es) = apply (VNat (m + n)) es
apply (VNat m) ((ETimes (VNat n)):es) = apply (VNat (m + n)) es
apply v [] = pure v
apply v es = pure $ v :$ es

evalTerm :: Valuable (Term d k) => [Decl] -> WC (Term d k) -> Either Error Value
evalTerm env = runExcept . eval [] . fmap (expandDecls env)
