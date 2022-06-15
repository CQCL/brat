{-# LANGUAGE FlexibleContexts #-}

module Brat.Checker.Helpers (evalNat
                            ,pullPorts, simpleCheck
                            ,combineDisjointEnvs
                            ,ensureEmpty, noUnders
                            ,rowToSig, sigToRow
                            ) where

import Brat.Checker.Monad (Checking, CheckingSig(..), err, typeErr)
import Brat.Error (ErrorMsg(..))
import Brat.Eval (Value(..), evalTerm)
import Brat.FC (WC(..))
import Brat.Naming (Name)
import Brat.Graph (Src)
import Brat.Syntax.Common
import Brat.Syntax.Core (Term)
import Brat.UserName (UserName)
import Control.Monad.Freer (req, Free(Ret))

import Control.Arrow ((***))
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
