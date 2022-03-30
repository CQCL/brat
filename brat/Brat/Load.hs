module Brat.Load (emptyMod
                 ,loadFile
                 ,loadFiles
                 ,LoadType(..)
                 ,typeGraph
                 ) where

import Brat.Checker
import Brat.Compile.Circuit
import Brat.Dot
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

import Control.Monad (foldM, unless, when)
import Control.Monad.Except
import Data.Array ((!))
import Data.Bifunctor
import Data.Either (isLeft)
import Data.Functor  (($>), (<&>))
import Data.List (init, isSuffixOf, elemIndex, take)
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.HT (viewR)
import qualified Data.Graph as G
import Data.Maybe (fromJust)
import Data.List.NonEmpty (nonEmpty)
import System.Directory (doesFileExist)
import System.FilePath

import Debug.Trace

-- A Module is a node in the dependency graph
type RawMod = (RawEnv, UserName, [UserName])
type Mod = (VEnv, [Decl], [TypedHole], Graph)
data LoadType = Lib | Exe deriving (Eq, Show)

emptyMod :: Mod
emptyMod = ([], [], [], ([], []))

addNounsToEnv :: Prefix -> [Decl] -> VEnv
addNounsToEnv pre = aux root
 where
  aux :: Namespace -> [Decl] -> VEnv
  aux _ [] = []
  aux namespace (Decl{..}:decls) =
    let (freshName, newNamespace) = fresh fnName namespace
        new = (PrefixName pre fnName, [ ((freshName, port), ty) | (port, ty) <- fnSig ])
    in  new : aux newNamespace decls

checkDecl :: Prefix -> Decl -> Checking ()
checkDecl pre Decl{..}
  | Local <- fnLocality = do
  tgt <- next fnName Id fnSig fnSig
  case fnBody of
    NoLhs body -> do
      ((), ((), [])) <- wrapError (addSrc fnName) $
                        (check body ((), [((tgt, port), ty) | (port, ty) <- fnSig]))
      pure ()
    ThunkOf verb -> do
      let ((_, C (ss :-> ts)):_) = merge fnSig
      src <- next (name <> "/in") Source ss ss
      tgt <- next (name <> "/out") Target ts ts
      let thunkTy = ("value", C (ss :-> ts))
      thunk <- next (name ++ "_thunk") (src :>>: tgt) [] [thunkTy]
      eval  <- next ("Eval(" ++ name ++ ")") (Eval (thunk, "value")) (thunkTy:ss) ts
      wire ((thunk, "value"), Right (snd thunkTy), (eval, "value"))
      ((), ([], [])) <- wrapError (addSrc name) $
                        checkClauses (unWC verb) ([((src, port), ty) | (port, ty) <- ss]
                                                 ,[((tgt, port), ty) | (port, ty) <- ts])
      pure ()

    Undefined -> error "No body in `checkDecl`"

  | Extern sym <- fnLocality = () <$ next (show $ PrefixName pre fnName) (Prim sym) [] fnSig
 where
  name = show $ PrefixName pre fnName

typeGraph :: VEnv -> Decl -> Either Error Graph
typeGraph venv fn = do
  (_, (_, g)) <- run (venv, [], fnLoc fn) (checkDecl [] fn)
  pure g

loadStmtsWithEnv :: Mod -> Prefix -> LoadType -> RawEnv -> Either Error Mod
loadStmtsWithEnv e@(venv, decls, holes, graph) pre loadType stmts = do
  newDecls <- desugarEnv stmts
  decls <- pure (decls ++ newDecls)
  -- hacky mess - cleanup!
  unless (null (duplicates decls)) $
    Left . Err Nothing Nothing . NameClash $ show (duplicates decls)
  venv <- pure $ venv <> addNounsToEnv pre decls
  -- giving a dummy file context - not ideal
  let env = (venv, decls, FC (Pos 0 0) (Pos 0 0))
  (_, (holes, graph))   <- run env (mapM (\d -> localFC (fnLoc d) $ checkDecl pre d) decls)

  -- all good? Let's just get the graph for `main` (and assume it's a noun)
  when (loadType == Exe) $ do
    main <- maybeToRight (Err Nothing Nothing MainNotFound) $ lookupBy ((=="main") . fnName) id decls
    (_, (_, mgraph)) <- run env (checkDecl [] main)
    pure ()

  pure (venv, decls, holes, graph)

loadFile :: LoadType -> FilePath -> String -> ExceptT Error IO Mod
loadFile lt path fname = do
  contents <- lift $ readFile (path </> (dropExtension fname) ++ ".brat")
  loadFiles lt path fname contents

-- Does not read the main file, but does read any imported files
loadFiles :: LoadType -> FilePath -> String -> String
         -> ExceptT Error IO Mod
loadFiles lt path fname contents = do
  let fn = plain fname
  edges <- depGraph [] fn contents

  let (g, f, _) = G.graphFromEdges edges
  let files = G.topSort (G.transposeG g)
  let getStmts v = let (stmts, (PrefixName ps name), _) = (f v) in ((ps ++ [name]), stmts)
  let allStmts = (map getStmts files) :: [(Prefix, RawEnv)]
  -- the original file should be at the end of the allStmts list:
  let (Just (rest, (prf, mainStmts))) = viewR allStmts
  unless (prf == [fname]) $
    throwError (dumbErr (InternalError "Top of dependency graph wasn't main file"))
  env <- liftEither $ foldM
         (\e (prefix,stmts) -> loadStmtsWithEnv e prefix Lib stmts) emptyMod
         rest
  liftEither $ loadStmtsWithEnv env [] lt mainStmts
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
