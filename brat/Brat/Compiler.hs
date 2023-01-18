module Brat.Compiler (printAST, printDeclsHoles, writeDot, compileFile) where

import Brat.Compile.Circuit
import Brat.Syntax.Common (Decl'(..), CType'(..), Modey(..), pattern R)
import Brat.Syntax.Value (Value(..))
import Brat.UserName
import Brat.Error
import Brat.Load
import Bwd (Bwd(..))
import Util

import Control.Monad.Except
import qualified Data.ByteString as BS
import Data.ProtoLens (encodeMessage)
import System.FilePath (dropExtension)
import Brat.Elaborator
import Brat.Dot (toDotString)

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
  (_, env@(decls,_)) <- eitherIO $ parseFile file cts
  banner "Flat AST" $ mapM_ print decls
  env'@(decls, _, _) <- eitherIO $ addSrcContext file cts (elabEnv env)
  when printRaw $ banner "Raw AST" $ mapM_ print decls
  when printAST $
    banner "desugared AST" (mapM_ print =<< eitherIO (addSrcContext file cts (desugarEnv env')))

writeDot :: String -> String -> IO ()
writeDot file out = do
  env <- runExceptT $ loadFilename file
  (_, _, _, graphs) <- eitherIO env
  case filter isMain graphs of
    [(_, g)] -> writeFile out (toDotString g)
    [] -> error "No main graph found!"
    _ -> error "More than one main graph found!"
 where
  isMain (PrefixName [] "main", _) = True
  isMain _ = False

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
    [(_, Right (VFun Kerny B0 (ss :-> ts)))] -> do
      let bin = wrapCircuit (compileCircuit graph (R ss, R ts))
      BS.writeFile outFile (encodeMessage bin)
      putStrLn $ "Wrote to file " ++ outFile
    -- Placeholder while tierkreis output is under development
    _ -> error "main function must be a kernel"
