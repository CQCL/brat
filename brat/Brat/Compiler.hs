module Brat.Compiler (printAST, printDeclsHoles, compileFile) where

import Brat.Compile.Circuit
import Brat.Syntax.Common (Decl'(..), VType'(..))
import Brat.UserName
import Brat.Error
import Brat.Load
import Util

import Control.Monad.Except
import qualified Data.ByteString as BS
import Data.ProtoLens (encodeMessage)
import System.FilePath (dropExtension)
import Brat.Elaborator

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
  (_, env) <- eitherIO $ parseFile file cts
  env'@(decls, _) <- eitherIO $ addSrcContext file cts (elabEnv env)
  when printRaw $ banner "Raw AST" $ mapM_ print decls
  when printAST $
    banner "desugared AST" (mapM_ print =<< eitherIO (addSrcContext file cts (desugarEnv env')))

compileFile :: String -> IO ()
compileFile file = do
  env <- runExceptT $ loadFilename file
  (_, decls, _, named_gs) <- eitherIO env
  -- Check main exists. (Will/should this work if "main" is in an imported module?)
  mn <- eitherIO $
      maybeToRight (addSrcName file $ dumbErr MainNotFound) $
      lookupBy ((== "main") . fnName) id decls

  (_name, graph) <- eitherIO $
      maybeToRight (addSrcName file $ dumbErr $ InternalError "No graph produced for main") $
      lookupBy ((== (PrefixName [] "main")) . fst) id named_gs

  let outFile = (dropExtension file) <> ".tk"
  case fnSig mn of
    [(_, K ss ts)] -> do
      let bin = wrapCircuit (compileCircuit graph (ss, ts))
      BS.writeFile outFile (encodeMessage bin)
      putStrLn $ "Wrote to file " ++ outFile
    -- Placeholder while tierkreis output is under development
    _ -> error "main function must be a kernel"
