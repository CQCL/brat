module Test.Parsing (getParsingTests, expectedParsingFails, expectFailForPaths) where

import Brat.Load
import Brat.Parser

import Control.Monad.Except
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

testParse :: FilePath -> TestTree
testParse file = testCase (show file) $ do
  cts <- readFile file
  case parseFile file cts of
    Left err -> assertFailure (show err)
    Right _ -> return () -- OK

expectedParsingFails = map ("examples" </>) [
    "thin.brat"]

expectFailForPaths :: [FilePath] -> (FilePath -> TestTree) -> FilePath -> TestTree
expectFailForPaths xf f path = (if path `elem` xf then expectFail else id) $ f path

parseXF = expectFailForPaths expectedParsingFails testParse

getParsingTests :: IO TestTree
getParsingTests = testGroup "parsing" . fmap parseXF <$> findByExtension [".brat"] "examples"
