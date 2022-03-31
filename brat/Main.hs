import Brat.Compiler

import Options.Applicative

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
  (if compile then compileFile else printDeclsHoles) file
