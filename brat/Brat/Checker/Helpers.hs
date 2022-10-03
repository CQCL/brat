{-# LANGUAGE FlexibleContexts #-}

module Brat.Checker.Helpers (evalNat
                            ,pullPorts, simpleCheck
                            ,combineDisjointEnvs
                            ,ensureEmpty, noUnders
                            ,rowToSig, sigToRow, subtractSig
                            ,showMode, getVec
                            ,mkThunkTy, getThunks
                            ,checkWire
                            ,selectorOutputs
                            ) where

import Brat.Checker.Monad (Checking, CheckingSig(..), err, typeErr, anext, awire)
import Brat.Checker.Types (Mode(..), Modey(..), Overs, Unders, ValueType)
import Brat.Error (ErrorMsg(..))
import Brat.Eval (Value(..), evalTerm)
import Brat.FC (WC(..))
import Brat.Naming (Name)
import Brat.Graph (DataNode(..), Src, Tgt, Thing(..))
import Brat.Syntax.Common
import Brat.Syntax.Core (Term(..))
import Brat.UserName (UserName)
import Control.Monad.Freer (req, Free(Ret))

import Control.Arrow ((***))
import Data.Functor (($>))
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding (last)

simpleCheck :: SimpleType -> SimpleTerm -> Checking ()
simpleCheck Natural (Num n) | n >= 0 = pure ()
simpleCheck IntTy (Num _) = pure ()
simpleCheck Boolean (Bool _) = pure ()
simpleCheck FloatTy (Float _) = pure ()
simpleCheck TextType (Text _) = pure ()
simpleCheck UnitTy Unit = pure ()
simpleCheck ty tm = fail (unwords [show tm, "is not of type", show ty])

pullPorts :: [Port] -> [((Name, Port), ty)] -> Checking [((Name, Port), ty)]
pullPorts [] types = pure types
pullPorts (p:ports) types = do
  (x, types) <- pull1Port p types
  (x:) <$> pullPorts ports types
 where
  pull1Port :: Port -> [((Name, Port), ty)]
            -> Checking (((Name, Port), ty), [((Name, Port), ty)])
  pull1Port p [] = fail $ "Port not found: " ++ p
  pull1Port p (x@((_, p'), _):xs)
   | p == p' = pure (x, xs)
   | otherwise = (id *** (x:)) <$> pull1Port p xs

evalNat :: Term Chk Noun -> Checking Int
evalNat tm = do
  env <- req Decls
  fc <- req AskFC
  case evalTerm env (WC fc tm) of
    Right (VSimple (Num n)) -> pure n
    Right v -> err $ VecEval (show v)
    Left er -> req $ Throw er

combineDisjointEnvs :: M.Map UserName v -> M.Map UserName v -> Checking (M.Map UserName v)
combineDisjointEnvs l r =
  let commonKeys = S.intersection (M.keysSet l) (M.keysSet r)
  in if S.null commonKeys
    then Ret $ M.union l r
    else typeErr ("Variable(s) defined twice: " ++
      (intercalate "," $ map show $ S.toList commonKeys))

ensureEmpty :: Show ty => String -> [(Src, ty)] -> Checking ()
ensureEmpty _ [] = pure ()
ensureEmpty str (x:xs) = err $ InternalError $ "Expected empty " ++ str ++ ", got:\n  " ++ showRow (x :| xs)

noUnders m = do
  (outs, (overs, unders)) <- m
  ensureEmpty "unders" unders
  pure (outs, overs)

sigToRow :: Traversable t => Name -> t (Port, ty) -> t (Src, ty)
sigToRow src = fmap $ \(p,ty) -> ((src, p), ty)

rowToSig :: Traversable t => t (Src, ty) -> t (Port, ty)
rowToSig = fmap $ \((_, p),ty) -> (p, ty)

showMode :: Modey m -> String
showMode Braty = ""
showMode Kerny = "(kernel) "

getVec :: Modey m -> ValueType m -> Maybe (ValueType m, Term Chk Noun)
getVec Braty (Vector ty n) = Just (ty, n)
getVec Kerny (Of ty n) = Just (ty, n)
getVec _ _ = Nothing

-- Ignores port names - appropriate only when the LHS (names) are specified by the user
subtractSig :: Eq a => [(Port, a)] -> [(Port,a)] -> Maybe [(Port, a)]
subtractSig xs [] = Just xs
subtractSig ((_,x):xs) ((_,y):ys) | x == y = subtractSig xs ys
subtractSig _ _ = Nothing

mkThunkTy :: Modey m -> [(Port, ValueType m)] -> [(Port, ValueType m)] -> VType' Term
mkThunkTy Braty ss ts = C (ss :-> ts)
mkThunkTy Kerny ss ts = K (R ss) (R ts)

-- Unders and Overs here are respectively the inputs and outputs for the thunks
-- This is the dual notion to the overs and unders used for typechecking against
-- Hence, we return them here in the opposite order to `check`'s connectors
getThunks :: Modey m
          -> [(Src, ValueType Brat)]
          -> Checking ([Name]
                      ,Unders m Chk
                      ,Overs m Verb
                      )
getThunks _ [] = pure ([], [], [])
getThunks m ((src, ty):rest)
 | Just (ss, ts) <- isThunkType m ty = do
  node <- let ?my = m in anext "" (Eval src) ss ts
  let counders = sigToRow node ss
  let coovers = sigToRow node ts
  (nodes, counders', coovers') <- getThunks m rest
  pure (node:nodes, counders <> counders', coovers <> coovers')
 where
  isThunkType :: Modey m -> ValueType Brat
              -> Maybe ([(Port, ValueType m)], [(Port, ValueType m)])
  isThunkType Braty (C (ss :-> ts)) = Just (ss, ts)
  isThunkType Kerny (K (R ss) (R ts)) = Just (ss, ts)
  isThunkType _ _ = Nothing
getThunks _ _ = typeErr "Force called on non-thunk"

checkWire :: (Eq (ValueType m), ?my :: Modey m)
          => (Src, ValueType m)
          -> (Tgt, ValueType m)
          -> Checking (Maybe ())
checkWire (src, oTy) (tgt, uTy) | oTy == uTy = awire (src, oTy, tgt) $> Just ()
checkWire _ _ = pure Nothing

-- Inputs, Outputs
selectorOutputs :: Modey m -> DataNode -> ValueType m
                -> Maybe [(Port, ValueType m)]
-- Note: this is the only Kerny selector
selectorOutputs Kerny DCons (Of elTy (Simple (Num n)))
  = Just [("head", elTy), ("tail", Of elTy (Simple (Num (n - 1))))]
selectorOutputs Braty DCons (List ty)
  = Just [("head", ty), ("tail", List ty)]
selectorOutputs Braty DCons (Vector elTy (Simple (Num n)))
  = Just [("head", elTy), ("tail", Vector elTy (Simple (Num (n - 1))))]
selectorOutputs Braty DSome (Option ty) = Just [("value", ty)]
selectorOutputs Braty DPair (Product s t) = Just [("first", s), ("second", t)]
selectorOutputs Braty DDoub ty = Just [("value", ty)]
selectorOutputs Braty DSucc ty = Just [("value", ty)]
selectorOutputs _ _ _ = Nothing
