{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

module Brat.Eval (evalTerm, Value(..)) where

import Brat.Error
import Brat.FC
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Thin

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
 | VTh Thinning
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

instance Valuable (Pattern (WC (Term Chk Noun))) where
  eval = evalPat
  eval' = evalPat'

err :: String -> Except Error a
err msg = throwError (Err Nothing Nothing (EvalErr msg))

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
ceval' g (Vec ts) = VVec <$> mapM (ceval g) ts
ceval' g (Emb tm) = seval g tm
-- eval g (Closure [Value] (Term d k)

-- These don't work because we need to hold onto the big end
ceval' g (Slice bigEnd slice) = do
  bigEnd <- evalNat g bigEnd
  slice <- mapM (evalNat g) slice
  pure $ evalSlice bigEnd slice
ceval' g (Pattern pat) = eval g pat
ceval' _ tm = throwError $ Err Nothing Nothing (Unimplemented "ceval" [show tm])

seval :: [Value] -> WC (Term Syn k) -> Eval Value
seval g (WC fc tm) = addFCToError fc (seval' g tm)

seval' :: [Value] -> Term Syn k -> Eval Value
seval' g (tm ::: _) = ceval g tm
seval' g (fun :$: arg) = do
  fun <- seval g fun
  arg <- ceval g arg
  apply fun [EApp arg]
seval' g (_ :\: body) = eval g body
seval' _ tm = throwError $ Err Nothing Nothing (Unimplemented "seval" [show tm])

evalPat :: [Value] -> WC (Pattern (WC (Term Chk Noun))) -> Eval Value
evalPat g (WC fc pat) = addFCToError fc (evalPat' g pat)

evalPat' :: [Value] -> Pattern (WC (Term Chk Noun)) -> Eval Value
evalPat' g (POnePlus tm) = eval g tm >>= flip apply [EPlus (VNat 1)]
evalPat' g (PTwoTimes tm) = eval g tm >>= flip apply [ETimes (VNat 2)]
evalPat' _ PNil = pure $ VVec []
evalPat' g (PCons tm)
  -- Only work if `tm` is the simplest version
  | (x :|: xs) <- unWC tm = do
  x <- eval g x
  xs <- eval g xs
  case xs of
    VVec xs -> pure $ VVec (x:xs)
    _ -> pure $ VCons x xs
  | otherwise = throwError $ Err Nothing Nothing (BadCons (show tm))
evalPat' g (PSome x) = VSome <$> eval g x
evalPat' _ PNone = pure VNone

pattern VNat n = VSimple (Num n)

apply :: Value -> [Elim] -> Eval Value
apply (VClos g v) (EApp v':es) = eval' (v':g) v >>= flip apply es
apply (VNat m) ((EPlus (VNat n)):es) = apply (VNat (m + n)) es
apply (VNat m) ((ETimes (VNat n)):es) = apply (VNat (m + n)) es
apply v [] = pure v
apply v es = pure $ v :$ es

evalNat :: [Value] -> WC (Term Chk Noun) -> Eval Int
evalNat g tm = do
  v <- ceval g tm
  case v of
    (VSimple (Num n)) -> pure n
    _ -> err $ "Couldn't compute a nat from " ++ show tm ++ ". Got " ++ show v

evalSlice :: Int -> Slice Int -> Value
evalSlice bigEnd (From n) = VTh (fromNatFrom bigEnd n)
evalSlice bigEnd (These []) = VTh (zeros bigEnd)
evalSlice bigEnd (These xs) = VTh $ foldr1 union (fromNat bigEnd <$> xs)

evalTerm :: Valuable (Term d k) => [Decl] -> WC (Term d k) -> Either Error Value
evalTerm env = runExcept . eval [] . fmap (expandDecls env)
