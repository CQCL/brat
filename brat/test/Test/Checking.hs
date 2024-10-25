module Test.Checking (parseAndCheck, getCheckingTests, expectedCheckingFails) where

import Brat.Load
import Brat.Naming (root)
import Test.Parsing (expectedParsingFails)
import Test.Util (expectFailForPaths)

import Control.Monad.Except
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver

expectedCheckingFails = map ("examples" </>) ["nested-abstractors.brat"
                                             ,"karlheinz_alias.brat"
                                             ,"hea.brat"
                                             ]

parseAndCheckXF :: FilePath -> TestTree
parseAndCheckXF = expectFailForPaths (expectedParsingFails ++ expectedCheckingFails) (parseAndCheck [])

getCheckingTests :: IO TestTree
getCheckingTests = testGroup "checking" . fmap parseAndCheckXF <$> findByExtension [".brat"] "examples"

parseAndCheck :: [FilePath] -> FilePath -> TestTree
parseAndCheck libDirs file = testCase (show file) $ do
  env <- runExceptT $ loadFilename root libDirs file
  case env of
    Left err -> assertFailure (show err)
    Right (venv, nouns, holes, _, _) ->
      ((length venv) + (length nouns) + (length holes) > 0) @? "Should produce something"