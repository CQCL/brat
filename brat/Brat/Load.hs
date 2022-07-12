module Brat.Load (emptyMod
                 ,loadFilename
                 ,loadFiles
                 ,typeGraph
                 ,checkDecl
                 ) where

import Brat.Checker.Combine
import Brat.Checker.Helpers (sigToRow)
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
import Data.List.NonEmpty (NonEmpty(..), last, toList)
import qualified Data.Graph as G
import qualified Data.Map as M
import System.Directory (doesFileExist)
import System.FilePath

import Prelude hiding (last)

-- A Module is a node in the dependency graph
type RawMod = (RawEnv, UserName, [UserName])
type Mod = (VEnv, [Decl], [TypedHole], Graph)

emptyMod :: Mod
emptyMod = (M.empty, [], [], (M.empty, []))

addNounsToEnv :: Prefix -> [Decl] -> VEnv
addNounsToEnv pre = aux root
 where
  aux :: Namespace -> [Decl] -> VEnv
  aux _ [] = M.empty
  aux namespace (Decl{..}:decls) =
    let (freshName, newNamespace) = fresh fnName namespace
        newKey = PrefixName pre fnName
        newValue = [ ((freshName, port), ty) | (port, ty) <- fnSig ]
    in  M.insert newKey newValue $ aux newNamespace decls

checkDecl :: Prefix -> Decl -> Checking ()
checkDecl pre Decl{..}
  | Local <- fnLocality = do
  fnSig <- case fnSig of
    [] -> req $ Throw (Err (Just fnLoc) Nothing (EmptyRow fnName))
    (x:xs) -> pure (x :| xs)
  tgt <- next fnName Id (toList fnSig) (toList fnSig)
  case fnBody of
    NoLhs body -> do
      ((), ((), [])) <- wrapError (addSrc fnName) $
                        let ?my = Braty in check body ((), toList (sigToRow tgt fnSig))
      pure ()
    ThunkOf verb -> do
      let outputs = sigToRow (MkName []) fnSig
      rows <- combinationsWithLeftovers outputs
      case last rows of
        ((_, C (ss :-> ts)), []) -> do
          src <- next (name <> "/in") Source ss ss
          tgt <- next (name <> "/out") Target ts ts
          let thunkTy = ("value", C (ss :-> ts))
          thunk <- next (name ++ "_thunk") (src :>>: tgt) [] [thunkTy]
          eval  <- next ("Eval(" ++ name ++ ")") (Eval (thunk, "value")) (thunkTy:ss) ts
          wire ((thunk, "value"), snd thunkTy, (eval, "value"))
          ((), ([], [])) <- wrapError (addSrc name) $
                            checkClauses (unWC verb) ([((src, port), ty) | (port, ty) <- ss]
                                                     ,[((tgt, port), ty) | (port, ty) <- ts])
          pure ()
        _ -> req $ Throw (dumbErr (InternalError "Thunk type isn't (just) a computation"))

    Undefined -> error "No body in `checkDecl`"

  | Extern sym <- fnLocality = () <$ next (show $ PrefixName pre fnName) (Prim sym) [] fnSig
 where
  name = show $ PrefixName pre fnName

typeGraph :: VEnv -> Decl -> Either Error Graph
typeGraph venv fn = do
  (_, (_, g)) <- run (venv, [], fnLoc fn) (checkDecl [] fn)
  pure g

loadStmtsWithEnv :: Mod -> Prefix -> RawEnv -> Either Error Mod
loadStmtsWithEnv (venv, decls, _, _) pre stmts = do
  newDecls <- desugarEnv stmts
  decls <- pure (decls ++ newDecls)
  -- hacky mess - cleanup!
  unless (null (duplicates decls)) $
    Left . Err Nothing Nothing . NameClash $ show (duplicates decls)
  venv <- pure $ venv <> addNounsToEnv pre decls
  -- giving a dummy file context - not ideal
  let env = (venv, decls, FC (Pos 0 0) (Pos 0 0))
  (_, (holes, graph))   <- run env (mapM (\d -> localFC (fnLoc d) $ checkDecl pre d) decls)

  pure (venv, decls, holes, graph)

loadFilename :: String -> ExceptT Error IO Mod
loadFilename file = do
  unless (takeExtension file == ".brat") $ fail $ "Filename " ++ file ++ " must end in .brat"
  let (path, fname) = splitFileName $ dropExtension file
  contents <- lift $ readFile file
  loadFiles path fname contents

-- Does not read the main file, but does read any imported files
loadFiles :: FilePath -> String -> String
         -> ExceptT Error IO Mod
loadFiles path fname contents = do
  let fn = plain fname
  edges <- depGraph [] fn contents

  let (g, f, _) = G.graphFromEdges edges
  let files = G.topSort (G.transposeG g)
  let getStmts v = let (stmts, (PrefixName ps name), _) = (f v) in ((ps ++ [name]), stmts)
  let allStmts = (map getStmts files) :: [(Prefix, RawEnv)]
  -- the original file should be at the end of the allStmts list:
  case viewR allStmts of
    Just (rest, (prf, mainStmts)) -> do
      unless (prf == [fname]) $
        throwError (dumbErr (InternalError "Top of dependency graph wasn't main file"))
      env <- liftEither $ foldM
             (\e (prefix,stmts) -> loadStmtsWithEnv e prefix stmts) emptyMod
             rest
      liftEither $ loadStmtsWithEnv env [] mainStmts
    Nothing -> throwError (dumbErr (InternalError "Empty dependency graph"))
  where
    depGraph :: [UserName] -> UserName -> String -> ExceptT Error IO [RawMod]
    depGraph chain name cts = case elemIndex name chain of
      Just idx -> throwError $ Err Nothing (Just fname) (ImportCycle (show name) $ show $ chain!!(idx-1))
      Nothing -> do
        (imports, env) <- liftEither $ parseFile (nameToFile name) cts
        es <- forM imports $ \name' -> do
          let file = nameToFile name'
          exists <- lift $ doesFileExist file
          unless exists $
            throwError (Err Nothing (Just (nameToFile name)) (FileNotFound file))
          cts' <- lift $ readFile (nameToFile name')
          depGraph (name:chain) name' cts'
        pure ((env, name, imports):(concat es))

    nameToFile :: UserName -> String
    nameToFile (PrefixName ps file) = path </> (foldr (</>) file ps) ++ ".brat"
