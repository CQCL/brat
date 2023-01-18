import Brat.Compiler

import Control.Monad (when)
import Options.Applicative

data Options = Opt {
  ast     :: Bool,
  dot     :: String,
  compile :: Bool,
  file    :: String,
  raw     :: Bool
}

compileFlag :: Parser Bool
compileFlag = switch (long "compile" <> short 'c' <> help "Compile to TIERKREIS")

astFlag = switch (long "ast" <> help "Print desugared BRAT syntax tree")

rawFlag = switch (long "raw" <> help "Print raw BRAT syntax tree")

dotOption = strOption (long "dot" <> value "" <> help "Write graph in Dot format to the specified file")

opts :: Parser Options
opts = Opt <$> astFlag <*> dotOption <*> compileFlag <*> (strArgument (metavar "FILE")) <*> rawFlag

main = do
  Opt{..} <- execParser (info opts (progDesc "Compile a BRAT program"))
  when (ast || raw) $ printAST raw ast file
  when (dot /= "") $ writeDot file dot
  if compile then compileFile file else printDeclsHoles file
