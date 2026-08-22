module Test.Compile.Hugr (compileToOutput, getHoles) where

import Control.Monad (forM)
import qualified Data.ByteString as BS
import Data.ByteString.Lazy (ByteString)
import qualified Data.Map as M
import System.Console.ANSI (Color(..), ColorIntensity(..), ConsoleLayer(..), SGR(..), setSGRCode)
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Config (ValidationConfig(..))
import System.Process (readCreateProcessWithExitCode, shell)
import System.Exit (ExitCode(..))
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Options (lookupOption, OptionDescription(..))
import Test.Tasty.Providers (IsTest(..))
import Test.Tasty.Providers.ConsoleFormat (noResultDetails)
import Test.Tasty.Runners (FailureReason(..), Result(..), Outcome(..), TestTree(..))

import Data.Proxy
import Data.Hugr (isHole)
import Data.HugrGraph (to_json, getOp, HugrGraph, getNodes)
import Data.List (sort)
import Data.Maybe (isJust)
import Brat.Compiler (compileFile, CompilingHoles(..))

data ValidationTest = VTest (IO ByteString) FilePath | Skipped String

instance IsTest ValidationTest where
  run opts (VTest hugr outFile) _ = do
    hugr_bytes <- hugr
    createDirectoryIfMissing True (takeDirectory outFile)
    BS.writeFile outFile $! (BS.toStrict $ hugr_bytes)
    (exitCode, stdout, stderr) <- readCreateProcessWithExitCode (shell $ "cat " ++ outFile ++ " | hugr_validator") ""
    case exitCode of
        ExitSuccess -> makeRes (Success, "Validated hugr", "PASSED")
        _ -> case lookupOption @ValidationConfig opts of
          RunValidation -> makeRes (Failure TestDepFailed, stderr, "FAILED")
          -- should we include the error message in the output for the skipped case? It might be a useful diagnostic, or just noise.
          IgnoreValidation -> run opts (Skipped "Validation failed")
  run opts (Skipped msg) = makeRes (Success, msg, "SKIPPED")
makeRes (outcome, msg1, msg2) = pure $ Result outcome msg1 (yellowText msg2) 0.0 noResultDetails
 where
  yellowText text = setSGRCode [SetColor Foreground Vivid Yellow] ++ text ++ setSGRCode [Reset]

  testOptions = pure [Option (Proxy :: Proxy ValidationConfig)]


prefix = "test/compilation"
outputDir = prefix </> "output"

compileToOutput :: String -> FilePath -> TestTree
compileToOutput name file = do
    createDirectoryIfMissing False outputDir
    compileFile [] file >>= \case
        Right hs -> testGroup file $ mconcat <$> (forM (M.toList hs) $ \(boxName, (hugr, holes)) -> do
            sort (getHoles hugr) @?= sort holes
            -- ignore splices for now
            let outFile = outputDir </> replaceExtension (takeFileName file) ((show boxName) ++ ".json")
            pure $ SingleTest outFile (VTest (pure $ to_json hugr) outFile))
        Left (CompilingHoles _) -> pure $ SingleTest file (Skipped "Skipped as contains holes")

getHoles :: Ord a => HugrGraph a -> [a]
getHoles hg = [n | n <- getNodes hg, isJust (isHole $ getOp hg n)]
