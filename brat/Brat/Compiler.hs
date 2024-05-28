module Brat.Compiler (printAST
                     ,printDeclsHoles
                     ,writeDot
                     ,compileFile
                     ,compileAndPrintFile
                     ) where

import Brat.Compile.Hugr
import Brat.Dot (toDotString)
import Brat.Elaborator
import Brat.Error
import Brat.Load
import Brat.Naming (root, split)

import qualified Data.ByteString.Lazy as BS
import Control.Monad (when)
import Control.Monad.Except
import System.Exit (die)

printDeclsHoles :: [FilePath] -> String -> IO ()
printDeclsHoles libDirs file = do
  env <- runExceptT $ loadFilename root libDirs file
  (_, decls, holes, _, _) <- eitherIO env
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
  env <- runExceptT $ loadFilename root libDirs file
  (_, _, _, _, graph) <- eitherIO env
  writeFile out (toDotString graph)
{-
 where
  isMain (PrefixName [] "main", _) = True
  isMain _ = False
-}

compileFile :: [FilePath] -> String -> IO BS.ByteString
compileFile libDirs file = do
  let (checkRoot, newRoot) = split "checking" root
  env <- runExceptT $ loadFilename checkRoot libDirs file
  (venv, _, holes, defs, outerGraph) <- eitherIO env
  case holes of
    [] -> pure $ compile defs newRoot outerGraph venv
    xs -> die (show (CompilingHoles (show <$> xs)))

compileAndPrintFile :: [FilePath] -> String -> IO ()
compileAndPrintFile libDirs file = BS.putStr =<< compileFile libDirs file
