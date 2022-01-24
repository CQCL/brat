import Brat.Compile.Scheme
import Brat.Error
import Brat.Load

import Options.Applicative
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
  if compile
    then do let output = compileFile (nouns, verbs)
            let outFile = (dropExtension file) <> ".ss"
            writeFile outFile output
            putStrLn output
            putStrLn $ "Wrote to file " ++ outFile

    else do putStrLn "Nouns:"
            print nouns
            putStrLn ""
            putStrLn "Verbs:"
            print verbs
            putStrLn ""
            putStrLn "Holes:"
            mapM_ print holes
