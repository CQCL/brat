import Control.Monad (unless)
import System.Directory
import System.Exit (ExitCode(..))
import Data.ProtoLens.Setup

installEmacsMode :: IO ()
installEmacsMode = do
  cwd <- getCurrentDirectory
  home <- getHomeDirectory
  let src = cwd ++ "/emacs/"

  keepGoing <- doesPathExist src
  unless keepGoing (error "I'm so confused")

  let dest = home ++ "/.local/share/brat/"
  () <- createDirectoryIfMissing True dest

  let bratMode = "brat-mode.el"
  let bratLsp  = "lsp-brat.el"

  copyFile (src ++ bratMode) (dest ++ bratMode)
  copyFile (src ++ bratLsp)  (dest ++ bratLsp)

  putStrLn $ "Copied emacs files to " ++ show dest


main = installEmacsMode *> defaultMainGeneratingProtos "proto/"

