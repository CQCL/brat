{-# LANGUAGE FlexibleContexts #-}

module Brat.Load (loadFilename
                 ,loadFiles
                 ,parseFile
                 ,desugarEnv
                 ) where

import Brat.Checker.Helpers (mkThunkTy, anext)
import Brat.Checker.Monad
import Brat.Checker.Types (ValueType)
import Brat.Checker
import Brat.Error
import Brat.FC
import Brat.Graph (Thing(..))
import Brat.Naming
import Brat.Parser
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.Raw
import Brat.UserName
import Control.Monad.Freer (req)
import Util

import Control.Monad.Except
import Data.List (elemIndex)
import Data.List.HT (viewR)
import Data.List.NonEmpty (NonEmpty(..), toList)
import qualified Data.Graph as G
import qualified Data.Map as M
import System.Directory (doesFileExist)
import System.FilePath

import Prelude hiding (last)

-- A Module is a node in the dependency graph
type RawMod = ((RawEnv, String) -- data at the node: declarations, and file contents
              ,UserName -- name of this node
              ,[UserName]) -- other nodes on which this depends
-- Result of checking/compiling a module
type Mod = (VEnv, [Decl]         -- all symbols from all modules
           ,[TypedHole]          -- for just the last module
           ,[(UserName, Graph)]) -- per function, first elem is name

addNounsToEnv :: Prefix -> [Decl] -> VEnv
addNounsToEnv pre = aux root
 where
  aux :: Namespace -> [Decl] -> VEnv
  aux _ [] = M.empty
  aux namespace (Decl{..}:decls) =
    let (freshName, newNamespace) = fresh fnName namespace
        newKey = PrefixName pre fnName
        newValue = [ (NamedPort (Ex freshName i) port, ty)
                   | (i, (port, ty)) <- zip [0..] fnSig ]
    in  M.insert newKey newValue $ aux newNamespace decls

checkDecl :: Prefix -> Decl -> Checking ()
checkDecl pre Decl{..}
  | Local <- fnLocality = do
  fnSig <- case fnSig of
    [] -> req $ Throw (Err (Just fnLoc) (EmptyRow fnName))
    (x:xs) -> pure (x :| xs)
  (_, unders, _) <- next fnName Id (toList fnSig) (toList fnSig)
  case fnBody of
    NoLhs body -> do
      ((), ((), [])) <- let ?my = Braty in check body ((), unders)
      pure ()
    -- TODO: Unify this with `getThunks` and `check (Th _)` code
    ThunkOf verb -> do
      case unders of
        [u] -> do
          case u of
            (_, C (ss :-> ts)) -> let ?my = Braty in checkThunk verb ss ts
            (_, K (R ss) (R ts)) -> let ?my = Kerny in checkThunk verb ss ts
            _ -> req $ Throw (dumbErr (ExpectedThunk "" (show u)))
        [] -> err $ EmptyRow name
        _ -> err $ MultipleOutputsForThunk name
    Undefined -> error "No body in `checkDecl`"

  | Extern sym <- fnLocality = () <$ next (show $ PrefixName pre fnName) (Prim sym) [] fnSig
 where
  name = show $ PrefixName pre fnName

  checkThunk :: (?my :: Modey m, CheckConstraints m)
             => WC (Clause Term Verb) -> [(PortName, ValueType m)] -> [(PortName, ValueType m)] -> Checking ()
  checkThunk verb ss ts = do
   (src, [], overs) <- anext (name <> "/in") Source [] ss
   (tgt, unders, []) <- anext (name <> "/out") Target ts []
   let thunkTy = ("value", mkThunkTy ?my ss ts)
   next (name ++ "_thunk") (src :>>: tgt) [] [thunkTy]
   ((), ([], [])) <- checkClauses (unWC verb) (overs, unders)
   pure ()

loadStmtsWithEnv :: (VEnv, [Decl]) -> (String, Prefix, RawEnv, String) -> Either SrcErr Mod
loadStmtsWithEnv (venv, decls) (fname, pre, stmts, cts) = do
  decls <- (decls ++) <$> addSrcContext fname cts (desugarEnv stmts)
  -- hacky mess - cleanup!
  unless (null (duplicates decls)) $
    Left (addSrcName fname $ dumbErr $ NameClash $ show (duplicates decls))
  let venv' = venv <> addNounsToEnv pre decls
  (holes, graph, _nsp) <- foldM (checkDecl' venv' decls pre) ([], [], root) decls

  pure (venv', decls, holes, graph)
 where
  -- A composable version of `checkDecl`
  checkDecl' :: VEnv -> [Decl] -> Prefix -- static environment, context
            -> ([TypedHole], [(UserName, Graph)], Namespace) -- 'fold' state: compiled output + namespace
            -> Decl -- to check
            -> Either SrcErr ([TypedHole], [(UserName, Graph)], Namespace)
  checkDecl' venv decls pre (holes, graphs, nsp) d = do
    let (decl_nsp, nsp') = split (fnName d) nsp
    ((), (holes', graph)) <- addSrcContext ((fnName d) ++ " (" ++ fname ++ ")") cts $
                                run (venv, decls, fnLoc d) decl_nsp (checkDecl pre d)
    pure (holes ++ holes', (PrefixName pre (fnName d), graph):graphs, nsp')


loadFilename :: String -> ExceptT SrcErr IO Mod
loadFilename file = do
  unless (takeExtension file == ".brat") $ fail $ "Filename " ++ file ++ " must end in .brat"
  let (path, fname) = splitFileName $ dropExtension file
  contents <- lift $ readFile file
  loadFiles path fname contents

-- Does not read the main file, but does read any imported files
loadFiles :: FilePath -> String -> String
         -> ExceptT SrcErr IO Mod
loadFiles path fname contents = do
  let fn = plain fname
  edges <- depGraph [] fn contents
  let (g, f, _) = G.graphFromEdges edges
  let files = G.topSort (G.transposeG g)
  let getStmts v = let ((stmts, cts), (PrefixName ps name), _) = f v in ((ps ++ [name]), stmts, cts)
  let allStmts = (map getStmts files) :: [(Prefix, RawEnv, String)]
  -- remove the prefix for the starting file
  allStmts' <- case viewR allStmts of
    -- the original file should be at the end of the allStmts list
    Just (rest, (mainPrf, mainStmts, mainCts)) -> do
      unless (mainPrf == [fname]) $
        throwError (SrcErr "" $ dumbErr (InternalError "Top of dependency graph wasn't main file"))
      pure $ [(path </> (foldr1 (</>) prf) ++ ".brat", prf, stmts, cts) | (prf, stmts, cts) <- rest]
             ++ [(path </> fname ++ ".brat", [], mainStmts, mainCts)]
    Nothing -> throwError (SrcErr "" $ dumbErr (InternalError "Empty dependency graph"))
    -- keep (as we fold) and then return only the graphs from the last file in the list
  liftEither $ foldM
    (\(venv, decls, _, _) -> loadStmtsWithEnv (venv, decls))
    (M.empty, [], [], [])
    allStmts'
  where
    depGraph :: [UserName] -> UserName -> String -> ExceptT SrcErr IO [RawMod]
    depGraph chain name cts = case elemIndex name chain of
      Just idx -> throwError $ addSrcName (nameToFile name) $ dumbErr (ImportCycle (show name) $ show $ chain!!(idx-1))
      Nothing -> do
        (imports, env) <- liftEither $ parseFile (nameToFile name) cts
        es <- forM imports $ \name' -> do
          let file = nameToFile name'
          exists <- lift $ doesFileExist file
          unless exists $
            throwError $ addSrcName (nameToFile name) $ dumbErr (FileNotFound file)
          cts' <- lift $ readFile file
          depGraph (name:chain) name' cts'
        pure (((env, cts), name, imports):(concat es))

    nameToFile :: UserName -> String
    nameToFile (PrefixName ps file) = path </> (foldr (</>) file ps) ++ ".brat"
