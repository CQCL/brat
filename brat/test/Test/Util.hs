module Test.Util where

import Brat.Checker
import Brat.Checker.Monad
import Brat.Checker.Types (initStore, emptyEnv)
import Brat.Error
import Brat.FC
import Brat.Load
import Brat.Naming

import Control.Monad.Except
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure

runEmpty m = run emptyEnv initStore root m

assertChecking :: Checking a -> Assertion
assertChecking m = case runEmpty $ localFC (FC (Pos 0 0) (Pos 0 0)) m of
  Right _ -> pure ()
  Left err -> assertFailure (showError err)

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = testCase (show file) $ do
  env <- runExceptT $ loadFilename root libDirs file
  case env of
    Left err -> assertFailure (show err)
    Right (venv, nouns, holes, _, _) ->
      ((length venv) + (length nouns) + (length holes) > 0) @? "Should produce something"

expectFailForPaths :: [FilePath] -> (FilePath -> TestTree) -> FilePath -> TestTree
expectFailForPaths xf f path = (if path `elem` xf then expectFail else id) $ f path
