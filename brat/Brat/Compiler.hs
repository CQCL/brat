module Brat.Compiler (printDeclsHoles, compileFile) where

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

compileFile :: String -> IO ()
compileFile file = do
  env <- runExceptT $ loadFilename file
  (venv, decls, _, _) <- eitherIO env
  -- all good? Let's just get the graph for `main`
  mn <- eitherIO $
      maybeToRight (Err Nothing Nothing MainNotFound) $
      lookupBy ((== "main") . fnName) id decls
  eitherIO $ run (venv, decls, fnLoc mn) $ checkDecl [] mn

  graph <- eitherIO $ typeGraph venv mn
  let outFile = (dropExtension file) <> ".tk"
  case fnSig mn of
    [(_, K ss ts)] -> do
      let bin = wrapCircuit (compileCircuit graph (ss, ts))
      BS.writeFile outFile (encodeMessage bin)
      putStrLn $ "Wrote to file " ++ outFile
    -- Placeholder while tierkreis output is under development
    _ -> error "main function must be a kernel"
