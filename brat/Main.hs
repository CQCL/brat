import Brat.Compile.Circuit
import Brat.Compile.Dummy
import Brat.FC
import Brat.Syntax.Common (Decl(..), Row(..), VType'(..), Clause(..))
import Brat.Error
import Brat.Load
import Util

import qualified Data.ByteString as BS
import Options.Applicative
import Data.ProtoLens (encodeMessage)
import System.FilePath (dropExtension)

data Options = Opt {
  prelude :: Bool,
  compile :: Bool,
  file    :: String
}

preludeFlag :: Parser Bool
preludeFlag = switch (long "prelude" <> short 'p' <> help "Use prelude")

compileFlag :: Parser Bool
compileFlag = switch (long "compile" <> short 'c' <> help "Compile to TIERKREIS")

eitherIO :: Either Error a -> IO a
eitherIO (Left e) = fail (debug e)
eitherIO (Right a) = pure a

opts :: Parser Options
opts = Opt <$> preludeFlag <*> compileFlag <*> (strArgument (metavar "FILE"))

main = do
  Opt{..} <- execParser (info opts (progDesc "Compile a BRAT program"))
  env <- if prelude
         then do cts <- readFile "prelude.brat"
                 (nouns, verbs, _) <- eitherIO $ loadFile "prelude.brat" cts
                 pure (nouns, verbs)
         else pure ([], [])
  contents <- readFile file
  (nouns, verbs, holes) <- eitherIO (loadFileWithEnv env file contents)
  if not compile
    then do putStrLn "Nouns:"
            print nouns
            putStrLn ""
            putStrLn "Verbs:"
            print verbs
            putStrLn ""
            putStrLn "Holes:"
            mapM_ print holes

    else do mn <- eitherIO $
                  maybeToRight (Err Nothing Nothing MainNotFound) $
                  lookupBy ((== "main") . fnName) id nouns
            let outFile = (dropExtension file) <> ".tk"
            let [NounBody cls] = fnBody mn
            let [(_, K ss ts)] = fnSig mn
            let bin = wrapCircuit (compileCircuit (unWC cls) (ss, ts))
            BS.writeFile outFile (encodeMessage bin)
            putStrLn $ "Wrote to file " ++ outFile

