import Brat.Compile.Circuit
import Brat.Syntax.Common (Decl(..), VType'(..))
import Brat.Error
import Brat.Load
import Util

import Control.Monad.Except
import qualified Data.ByteString as BS
import Options.Applicative
import Data.ProtoLens (encodeMessage)
import System.FilePath (dropExtension, splitFileName)

data Options = Opt {
  compile :: Bool,
  file    :: String
}

compileFlag :: Parser Bool
compileFlag = switch (long "compile" <> short 'c' <> help "Compile to TIERKREIS")

opts :: Parser Options
opts = Opt <$> compileFlag <*> (strArgument (metavar "FILE"))

main = do
  Opt{..} <- execParser (info opts (progDesc "Compile a BRAT program"))
  contents <- readFile file
  (cwd, file) <- pure $ splitFileName $ dropExtension file
  if not compile
    then do env <- runExceptT $ loadFile Lib cwd file contents
            (cenv, venv, nouns, verbs, holes, _) <- eitherIO env
            putStrLn "Nouns:"
            print nouns
            putStrLn ""
            putStrLn "Verbs:"
            print verbs
            putStrLn ""
            putStrLn "Holes:"
            mapM_ print holes

    else do env <- runExceptT $ loadFile Exe cwd file contents
            (cenv, venv, nouns, verbs, holes, _) <- eitherIO env
            mn <- eitherIO $
                  maybeToRight (Err Nothing Nothing MainNotFound) $
                  lookupBy ((== "main") . fnName) id nouns
            graph <- eitherIO $ typeGraph (cenv, venv) mn
            let outFile = (dropExtension file) <> ".tk"
            let [(_, K ss ts)] = fnSig mn
            let bin = wrapCircuit (compileCircuit graph (ss, ts))
            BS.writeFile outFile (encodeMessage bin)
            putStrLn $ "Wrote to file " ++ outFile

