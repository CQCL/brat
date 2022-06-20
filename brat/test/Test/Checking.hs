module Test.Checking (getCheckingTests) where

import Brat.Load

import Control.Monad.Except
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

parseAndCheck :: FilePath -> TestTree
parseAndCheck file = testCase (show file) $ do
  env <- runExceptT $ loadFilename file
  case env of
    Left err -> assertFailure (show err)
    Right (venv, nouns, holes, _) -> do
      print holes
      ((length venv) + (length nouns) + (length holes) > 0) @? "Should produce something"

expectedFails = map ("examples" </>) ["composition.brat",
    "karlheinz.brat",
    "karlheinz_alias.brat",
    "thin.brat",
    "hea.brat"]


parseAndCheckXF :: FilePath -> TestTree
parseAndCheckXF path =
  (if path `elem` expectedFails then expectFail else id) $ parseAndCheck path

getCheckingTests :: IO TestTree
getCheckingTests = testGroup "checking" . fmap parseAndCheckXF <$> findByExtension [".brat"] "examples"
