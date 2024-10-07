module Test.Util where

import Brat.Checker
import Brat.Checker.Monad
import Brat.Checker.Types (initStore, emptyEnv)
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
import Data.List (isInfixOf)

runEmpty m = run emptyEnv initStore root m

assertChecking :: Checking a -> Assertion
assertChecking m = case runEmpty $ localFC (FC (Pos 0 0) (Pos 0 0)) m of
  Right _ -> pure ()
  Left err -> assertFailure (showError err)

assertCheckingFail :: Show a => String -> Checking a -> Assertion
assertCheckingFail needle m = case runEmpty $ localFC (FC (Pos 0 0) (Pos 0 0)) m of
  Right res -> assertFailure ("Computation produced result " ++ show res ++ " when should have Thrown")
  Left err -> let shown = showError err in
    if isInfixOf needle shown then pure () else assertFailure ("Unexpected error " ++ shown)

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = testCase (show file) $ do
  env <- runExceptT $ loadFilename root libDirs file
  case env of
    Left err -> assertFailure (show err)
    Right (venv, nouns, holes, _, _, _) ->
      ((length venv) + (length nouns) + (length holes) > 0) @? "Should produce something"
