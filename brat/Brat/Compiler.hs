module Brat.Compiler (printDeclsHoles, compileFile) where

import Brat.Compile.Circuit
import Brat.Syntax.Common (Decl'(..), VType'(..))
import Brat.Error
import Brat.Load
import Util

import Control.Monad.Except
import qualified Data.ByteString as BS
import Data.ProtoLens (encodeMessage)
import System.FilePath (dropExtension, splitFileName, takeExtension)

checkFilename file = do
  unless (takeExtension file == ".brat") $ fail $ "Filename " ++ file ++ " must end in .brat"
  pure $ splitFileName $ dropExtension file

printDeclsHoles :: String -> IO ()
printDeclsHoles file = do
  (cwd, file) <- checkFilename file
  env <- runExceptT $ loadFile Lib cwd file
  (_, decls, holes, _) <- eitherIO env
  putStrLn "Decls:"
  print decls
  putStrLn ""
  putStrLn "Holes:"
  mapM_ print holes

compileFile :: String -> IO ()
compileFile file = do
  (cwd, file) <- checkFilename file
  env <- runExceptT $ loadFile Exe cwd file
  (venv, decls, _, _) <- eitherIO env
  mn <- eitherIO $
      maybeToRight (Err Nothing Nothing MainNotFound) $
      lookupBy ((== "main") . fnName) id decls
  graph <- eitherIO $ typeGraph venv mn
  let outFile = (dropExtension file) <> ".tk"
  case fnSig mn of
    [(_, K ss ts)] -> do
      let bin = wrapCircuit (compileCircuit graph (ss, ts))
      BS.writeFile outFile (encodeMessage bin)
      putStrLn $ "Wrote to file " ++ outFile
    -- Placeholder while tierkreis output is under development
    _ -> error "main function must be a kernel"
