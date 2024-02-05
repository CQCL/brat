module Brat.Compiler (printAST, printDeclsHoles, writeDot, compileFile) where

import Brat.UserName
import Brat.Error
import Brat.Load
import Util

import Control.Monad.Except
import Brat.Elaborator
import Brat.Dot (toDotString)

printDeclsHoles :: [FilePath] -> String -> IO ()
printDeclsHoles libDirs file = do
  env <- runExceptT $ loadFilename libDirs file
  (_, decls, holes, _) <- eitherIO env
  putStrLn "Decls:"
  print decls
  putStrLn ""
  putStrLn "Holes:"
  mapM_ print holes

-- Print an 80 column banner as the header and footer of some IO action's output
banner :: String -> IO a -> IO a
banner s m = putStrLn startText *> m <* putStrLn endText
 where
  startText = dashes ++ " " ++ s ++ space ++ dashes
  endText = replicate 80 '-'

  -- Add an extra space if `s` is odd to pad to 80 chars
  space = ' ' : replicate (len `mod` 2) ' '
  dashes = replicate (39 - hlen) '-'
  len = length s + 2
  hlen = len `div` 2

printAST :: Bool -> Bool -> String -> IO ()
printAST printRaw printAST file = do
  cts <- readFile file
  (_, env@(decls,_)) <- eitherIO $ parseFile file cts
  banner "Flat AST" $ mapM_ print decls
  env'@(decls, _, _) <- eitherIO $ addSrcContext file cts (elabEnv env)
  when printRaw $ banner "Raw AST" $ mapM_ print decls
  when printAST $
    banner "desugared AST" (mapM_ print =<< eitherIO (addSrcContext file cts (desugarEnv env')))

writeDot :: [FilePath] -> String -> String -> IO ()
writeDot libDirs file out = do
  env <- runExceptT $ loadFilename libDirs file
  (_, _, _, graphs) <- eitherIO env
  case filter isMain graphs of
    [(_, g)] -> writeFile out (toDotString g)
    [] -> error "No main graph found!"
    _ -> error "More than one main graph found!"
 where
  isMain (PrefixName [] "main", _) = True
  isMain _ = False

compileFile :: [FilePath] -> String -> IO ()
compileFile libDirs file = do
  env <- runExceptT $ loadFilename libDirs file
  (_, decls, _, named_gs) <- eitherIO env
  -- Check main exists. (Will/should this work if "main" is in an imported module?)
  _mn <- eitherIO $
      maybeToRight (addSrcName file $ dumbErr MainNotFound) $
      lookup (plain "main") decls

  (_name, _graph) <- eitherIO $
      maybeToRight (addSrcName file $ dumbErr $ InternalError "No graph produced for main") $
      lookupBy ((== PrefixName [] "main") . fst) id named_gs

  pure ()
