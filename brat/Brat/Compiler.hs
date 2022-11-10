module Brat.Compiler (printAST, printDeclsHoles, compileFile) where

import Brat.Compile.Circuit
import Brat.Checker (run)
import Brat.Syntax.Common (Decl'(..), VType'(..))
import Brat.Error
import Brat.Load
import Util

import Control.Monad.Except
import qualified Data.ByteString as BS
import Data.ProtoLens (encodeMessage)
import System.FilePath (dropExtension)

printDeclsHoles :: String -> IO ()
printDeclsHoles file = do
  env <- runExceptT $ loadFilename file
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
  space = ' ' : (replicate (len `mod` 2) ' ')
  dashes = replicate (39 - hlen) '-'
  len = length s + 2
  hlen = len `div` 2
  
printAST :: Bool -> Bool -> String -> IO ()
printAST printRaw printAST file = do
  cts <- readFile file
  (_, env@(decls, _)) <- eitherIO $ parseFile file cts
  when printRaw $ banner "Raw AST" $ mapM_ print decls
  when printAST $
    banner "desugared AST" (mapM_ print =<< eitherIO (desugarEnv env))

compileFile :: String -> IO ()
compileFile file = do
  env <- runExceptT $ loadFilename file
  (venv, decls, _, _) <- eitherIO env
  -- all good? Let's just get the graph for `main`
  mn <- eitherIO $
      maybeToRight (dumbErr MainNotFound) $
      lookupBy ((== "main") . fnName) id decls
  eitherIO $ run (venv, decls, fnLoc mn) $ checkDecl [] mn

  (_, (_, graph)) <- eitherIO $ run (venv, [], fnLoc mn) (checkDecl [] mn)

  let outFile = (dropExtension file) <> ".tk"
  case fnSig mn of
    [(_, K ss ts)] -> do
      let bin = wrapCircuit (compileCircuit graph (ss, ts))
      BS.writeFile outFile (encodeMessage bin)
      putStrLn $ "Wrote to file " ++ outFile
    -- Placeholder while tierkreis output is under development
    _ -> error "main function must be a kernel"
