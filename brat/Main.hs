import Brat.Compiler

import Control.Monad (when)
import Options.Applicative

data Options = Opt {
  ast     :: Bool,
  compile :: Bool,
  file    :: String,
  raw     :: Bool
}

compileFlag :: Parser Bool
compileFlag = switch (long "compile" <> short 'c' <> help "Compile to TIERKREIS")

astFlag = switch (long "ast" <> help "Print desugared BRAT syntax tree")

rawFlag = switch (long "raw" <> help "Print raw BRAT syntax tree")

opts :: Parser Options
opts = Opt <$> astFlag <*> compileFlag <*> (strArgument (metavar "FILE")) <*> rawFlag

main = do
  Opt{..} <- execParser (info opts (progDesc "Compile a BRAT program"))
  when (ast || raw) $ printAST raw ast file
  (if compile then compileFile else printDeclsHoles) file
