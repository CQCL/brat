{-# LANGUAGE FlexibleContexts #-}

module Test.Util where

import Brat.Checker
import Brat.Checker.Monad
import Brat.Error
import Brat.FC
import Brat.Load
import Brat.Naming
import Brat.Syntax.Common (CType'(..), TypeKind)
import Brat.Syntax.Port
import Brat.Syntax.Value
import Bwd

import Control.Monad.Except
import Test.Tasty
import Test.Tasty.HUnit

runEmpty m = run emptyEnv root m

typeEqRow :: (DeBruijn (BinderType m), Show (BinderType m))
          => Modey m -> String
          -> [(PortName, BinderType m)] -- Expected
          -> [(PortName, BinderType m)] -- Actual
          -> EqEnv
          -> Checking EqEnv
typeEqRow m tm ss ts eqCtx = eqRow tm m eqCtx ss ts

assertChecking :: Checking a -> Assertion
assertChecking m = case runEmpty $ localFC (FC (Pos 0 0) (Pos 0 0)) m of
  Right _ -> pure ()
  Left err -> assertFailure (showError err)

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = testCase (show file) $ do
  env <- runExceptT $ loadFilename libDirs file
  case env of
    Left err -> assertFailure (show err)
    Right (venv, nouns, holes, _) ->
      ((length venv) + (length nouns) + (length holes) > 0) @? "Should produce something"
