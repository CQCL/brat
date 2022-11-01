{-# LANGUAGE FlexibleContexts #-}

module Brat.Checker.Helpers (evalNat
                            ,pullPorts, simpleCheck
                            ,combineDisjointEnvs
                            ,ensureEmpty, noUnders
                            ,rowToSig, subtractSig
                            ,showMode, getVec
                            ,mkThunkTy, getThunks
                            ,checkWire
                            ,conFields, patternToData
                            ,awire, wire, kwire
                            ,anext, next, knext
                            ) where

import Brat.Checker.Monad (Checking, CheckingSig(..), err, typeErr)
import Brat.Checker.Types (Mode(..), Modey(..), Overs, Unders, ValueType)
import Brat.Error (ErrorMsg(..))
import Brat.Eval (Value(..), evalTerm)
import Brat.FC (WC(..))
import Brat.Naming (Name)
import Brat.Graph (DataNode(..), Node(..), Thing(..))
import Brat.Syntax.Common
import Brat.Syntax.Core (Term(..), SType, VType)
import Brat.UserName (UserName(..))
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

pullPorts :: Show ty
          => [PortName]
          -> [((End, PortName), ty)]
          -> Checking [((End, PortName), ty)]
pullPorts [] types = pure types
pullPorts (p:ports) types = do
  (x, types) <- pull1Port p types
  (x:) <$> pullPorts ports types
 where
  pull1Port :: Show ty
            => PortName
            -> [((End, PortName), ty)]
            -> Checking (((End, PortName), ty), [((End, PortName), ty)])
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

rowToSig :: Traversable t => t (Src, ty) -> t (PortName, ty)
rowToSig = fmap $ \((_, p),ty) -> (p, ty)

showMode :: Modey m -> String
showMode Braty = ""
showMode Kerny = "(kernel) "

getVec :: Modey m -> ValueType m -> Maybe (ValueType m, Term Chk Noun)
getVec Braty (Vector ty n) = Just (ty, n)
getVec Kerny (Of ty n) = Just (ty, n)
getVec _ _ = Nothing

-- Ignores port names - appropriate only when the LHS (names) are specified by the user
subtractSig :: Eq a => [(PortName, a)] -> [(PortName,a)] -> Maybe [(PortName, a)]
subtractSig xs [] = Just xs
subtractSig ((_,x):xs) ((_,y):ys) | x == y = subtractSig xs ys
subtractSig _ _ = Nothing

anext :: (?my :: Modey m)
      => String -> Thing
      -> [(PortName, ValueType m)] -- Inputs and Outputs use deBruijn indices
      -> [(PortName, ValueType m)]
      -> Checking (Name, Unders m Chk, Overs m Verb)
anext str th ins outs = do
  node <- req (Fresh str) -- Pick a name for the thunk
  -- Use the new name to generate Ends with which to instantiate types
  let unders = [ (((node, In i), p), ty) | (i,(p,ty)) <- zip [0..] ins ]
  let overs  = [ (((node, Ex i), p), ty) | (i,(p,ty)) <- zip [0..] outs ]
  () <- req (AddNode node (mkNode ?my th ins outs))
  pure (node, unders, overs)
 where
  mkNode :: Modey m -> Thing
         -> [(PortName, ValueType m)]
         -> [(PortName, ValueType m)]
         -> Node
  mkNode Braty = BratNode
  mkNode Kerny = KernelNode

next :: String -> Thing
     -> [(PortName, ValueType Brat)]
     -> [(PortName, ValueType Brat)]
     -> Checking (Name, Unders Brat Chk, Overs Brat Verb)
next = let ?my = Braty in anext

knext :: String -> Thing
      -> [(PortName, ValueType Kernel)]
      -> [(PortName, ValueType Kernel)]
      -> Checking (Name, Unders Kernel Chk, Overs Kernel Verb)
knext = let ?my = Kerny in anext

awire :: (?my :: Modey m) => (End, ValueType m, End) -> Checking ()
awire (src@(_, Ex _), ty, tgt@(_, In _)) = do
  ty <- mkT ?my ty
  req $ Wire (src, ty, tgt)
 where
  mkT :: Modey m -> ValueType m -> Checking (Either SType VType)
  mkT Braty ty = pure $ Right ty
  mkT Kerny ty = pure $ Left ty

mkThunkTy :: Modey m -> [(PortName, ValueType m)] -> [(PortName, ValueType m)] -> VType' Term
mkThunkTy Braty ss ts = C (ss :-> ts)
mkThunkTy Kerny ss ts = K (R ss) (R ts)
wire = let ?my = Braty in awire
kwire = let ?my = Kerny in awire

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
  (node, counders, coovers) <- let ?my = m in anext "" (Eval src) ss ts
  (nodes, counders', coovers') <- getThunks m rest
  pure (node:nodes, counders <> counders', coovers <> coovers')
 where
  isThunkType :: Modey m -> ValueType Brat
              -> Maybe ([(PortName, ValueType m)], [(PortName, ValueType m)])
  isThunkType Braty (C (ss :-> ts)) = Just (ss, ts)
  isThunkType Kerny (K (R ss) (R ts)) = Just (ss, ts)
  isThunkType _ _ = Nothing
getThunks m (out:_) = err $ ExpectedThunk (showMode m) (showRow (out :| []))

checkWire :: (Eq (ValueType m), ?my :: Modey m)
          => (Src, ValueType m)
          -> (Tgt, ValueType m)
          -> Checking (Maybe ())
checkWire ((src,_), oTy) ((tgt,_), uTy) | oTy == uTy = awire (src, oTy, tgt) $> Just ()
checkWire _ _ = pure Nothing

conFields :: Modey m -> DataNode -> ValueType m
              -> Maybe [(PortName, ValueType m)]
-- Note: These are the only Kerny constructors
conFields Kerny DNil (Of _ (Simple (Num 0))) = Just []
conFields Kerny DCons (Of elTy (Simple (Num n))) | n > 0
  = Just [("head", elTy), ("tail", Of elTy (Simple (Num (n - 1))))]

conFields Braty DNil (List _) = Just []
conFields Braty DCons (List ty)
  = Just [("head", ty), ("tail", List ty)]

conFields Braty DNil (Vector _ (Simple (Num 0))) = Just []
conFields Braty DCons (Vector elTy (Simple (Num n))) | n > 0
  = Just [("head", elTy), ("tail", Vector elTy (Simple (Num (n - 1))))]

conFields Braty DNone (Option _) = Just []
conFields Braty DSome (Option ty) = Just [("value", ty)]
conFields Braty DPair (Product s t) = Just [("first", s), ("second", t)]
conFields Braty DDoub ty = Just [("value", ty)]
conFields Braty DSucc ty = Just [("value", ty)]
conFields _ _ _ = Nothing

patternToData :: Modey m -> String -> ValueType m
              -> Maybe DataNode
patternToData m c ty = case c of
  "succ" -> Just DSucc
  "doub" -> Just DDoub
  "cons" | (Braty, Product _ _) <- (m,ty) -> Just DPair
  "cons" -> Just DCons
  "some" -> Just DSome
  "none" -> Just DNone
  "nil" -> Just DNil
  _ -> Nothing
