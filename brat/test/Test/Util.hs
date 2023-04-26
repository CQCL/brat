{-# LANGUAGE FlexibleContexts #-}

module Test.Util where

import Brat.Checker
import Brat.Checker.Monad
import Brat.Error
import Brat.FC
import Brat.Naming
import Brat.Syntax.Common (CType'(..), TypeKind)
import Brat.Syntax.Port
import Brat.Syntax.Value
import Bwd

import Test.Tasty.HUnit

runEmpty m = run emptyEnv root m

typeEqRow :: (DeBruijn (BinderType m), Show (BinderType m))
          => Modey m -> String
          -> [(PortName, BinderType m)] -- Expected
          -> [(PortName, BinderType m)] -- Actual
          -> (Bwd (Int, TypeKind), Int) 
          -> Checking (Bwd (Int, TypeKind), Int)
typeEqRow m tm ss ts (ctx, i) = do
  ss <- evalRow (changeVars (InxToLvl ctx) 0 (doesItBind m) ss)
  ts <- evalRow (changeVars (InxToLvl ctx) 0 (doesItBind m) ts)
  eqRow tm m (ctx, i) ss ts
 where
  evalRow = traverse (evalOver m)

  evalOver :: Modey m -> (PortName, BinderType m) -> Checking (PortName, BinderType m)
  evalOver Braty (p, Right ty) = (p,) . Right <$> evTy ty
  evalOver Braty (p, Left k) = pure (p, Left k)
  evalOver Kerny (p, ty) = (p,) <$> evSTy ty

assertChecking :: Checking a -> Assertion
assertChecking m = case runEmpty $ localFC (FC (Pos 0 0) (Pos 0 0)) m of
  Right _ -> pure ()
  Left err -> assertFailure (showError err)
