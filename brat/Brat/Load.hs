{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Brat.Load (loadFilename
                 ,loadFiles
                 ,parseFile
                 ,desugarEnv
                 ) where

import Brat.Checker.Clauses
import Brat.Checker.Helpers (ensureEmpty)
import Brat.Checker.Monad
import Brat.Checker
import Brat.Elaborator (elabEnv)
import Brat.Error
import Brat.FC
import Brat.Graph (Thing(..))
import Brat.Naming
import Brat.Parser
import Brat.Syntax.Common
import Brat.Syntax.Concrete (FEnv)
import Brat.Syntax.Core
import Brat.Syntax.Raw
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Control.Monad.Freer (req)

import Control.Monad.Except
import Data.List (elemIndex)
import Data.List.HT (viewR)
import qualified Data.Graph as G
import qualified Data.Map as M
import System.Directory (doesFileExist)
import System.FilePath

-- A Module is a node in the dependency graph
type FlatMod = ((FEnv, String) -- data at the node: declarations, and file contents
               ,UserName -- name of this node
               ,[UserName]) -- other nodes on which this depends

-- Result of checking/compiling a module
type VMod = (VEnv, [VDecl]        -- all symbols from all modules
           ,[TypedHole]          -- for just the last module
           ,[(UserName, Graph)]) -- per function, first elem is name

emptyMod :: VMod
emptyMod = (M.empty, [], [], [])

-- kind check the signature of a function and add it to the environment
addNounsToEnv :: Prefix -> [Decl] -> Checking (VEnv, [VDecl])
addNounsToEnv _ [] = pure (M.empty, [])
addNounsToEnv pre (d@Decl{..}:decls) = do
  let newKey = PrefixName pre fnName
  sig <- kindCheckRow fnSig
  (venv, vdecls) <- addNounsToEnv pre decls
  (_, _, row, _) <- next fnName (Prim fnName) (B0,B0) [] sig
  pure (M.insert newKey row venv, d { fnSig = sig } : vdecls)

checkDecl :: Prefix -> VDecl -> Checking ()
checkDecl pre Decl{..}
  | Local <- fnLocality = localFC fnLoc $ do
  (_, unders, _, _) <- next fnName Id (B0, B0) fnSig fnSig
  case fnBody of
    NoLhs body -> do
      (((), ()), ((), [])) <- let ?my = Braty in check body ((), unders)
      pure ()
    -- TODO: Unify this with `getThunks` and `check (Th _)` code
    ThunkOf (WC _ verb) -> case fnSig of
      -- Seems like it should be important to not drop the context here
      [(_, Right (VFun m@Braty ctx (ss :-> ts)))] -> let ?my = m in checkBody fnName verb (ctx, ss, ts)
      [(_, Right (VFun m@Kerny ctx (ss :-> ts)))] -> let ?my = m in checkBody fnName verb (ctx, ss, ts)
      [u] -> req $ Throw (dumbErr $ ExpectedThunk "" (show u))
      [] -> err $ EmptyRow name
      (_:_) -> err $ MultipleOutputsForThunk name

    Undefined -> error "No body in `checkDecl`"

  | Extern sym <- fnLocality = () <$ next (show $ PrefixName pre fnName) (Prim sym) (B0,B0) [] fnSig
 where
  name = show $ PrefixName pre fnName

loadAlias :: TypeAlias -> Checking (UserName, [(PortName, TypeKind)], [ValPat], Value)
loadAlias (TypeAlias fc name args body) = localFC fc $ do
  (_, [(hhungry, Left k)], _, _) <- next "" Hypo (B0,B0) [("type", Left (Star args))] []
  let abs = WC fc $ foldr (:||:) AEmpty (APat . Bind . fst <$> args)
  ([v], unders) <- kindCheck [(hhungry, k)] $ Th (WC fc (abs :\: (WC fc body)))
  ensureEmpty "loadAlias unders" unders
  -- TODO: We give patterns here than can be used to restrict what arguments a 
  -- given type alias can receive. Currently, for simplicity, we make all of 
  -- these patterns `VPVar`. `VPVar` is the pattern which matches a term without 
  -- scrutinising it.
  let pats = [ VPVar | _ <- args]
  pure (name, args, pats, v)

withAliases :: [TypeAlias] -> Checking a -> Checking a
withAliases [] m = m
withAliases (a:as) m = loadAlias a >>= \a -> localAlias a $ withAliases as m

loadStmtsWithEnv :: (VEnv, [VDecl]) -> (String, Prefix, FEnv, String) -> Either SrcErr VMod
loadStmtsWithEnv (venv, oldDecls) (fname, pre, stmts, cts) = addSrcContext fname cts $ do
  -- hacky mess - cleanup!
  (decls, aliases) <- desugarEnv =<< elabEnv stmts
  {-
  unless (null (duplicates decls)) $
    Left (addSrcName fname $ dumbErr $ NameClash $ show (duplicates decls))
  -}
  ((venv', vdecls), (holes, graphs)) <- run venv root
                                        $ withAliases aliases $ do
    (venv, vdecls) <- addNounsToEnv pre decls
    localVEnv venv $ traverse (checkDecl pre) vdecls
    pure (venv, vdecls)
  
  pure (venv <> venv', oldDecls <> vdecls, holes, [(PrefixName [] "main", graphs)])
 where
  -- A composable version of `checkDecl`
  {-
  checkDecl' :: VEnv -> [VDecl] -> Prefix -- static environment, context
            -> ([TypedHole], [(UserName, Graph)], Namespace) -- 'fold' state: compiled output + namespace
            -> VDecl -- to check
            -> Either SrcErr ([TypedHole], [(UserName, Graph)], Namespace)
  checkDecl' venv decls pre (holes, graphs, nsp) d = do
    let (decl_nsp, nsp') = split (fnName d) nsp
    ((), (holes', graph)) <- addSrcContext ((fnName d) ++ " (" ++ fname ++ ")") cts $
                             venv decl_nsp (checkDecl pre d)
    pure (holes ++ holes', (PrefixName pre (fnName d), graph):graphs, nsp')
  -}


loadFilename :: String -> ExceptT SrcErr IO VMod
loadFilename file = do
  unless (takeExtension file == ".brat") $ fail $ "Filename " ++ file ++ " must end in .brat"
  let (path, fname) = splitFileName $ dropExtension file
  contents <- lift $ readFile file
  loadFiles path fname contents

-- Does not read the main file, but does read any imported files
loadFiles :: FilePath -> String -> String
         -> ExceptT SrcErr IO VMod
loadFiles path fname contents = do
  let fn = plain fname
  edges <- depGraph [] fn contents
  let (g, f, _) = G.graphFromEdges edges
  let files = G.topSort (G.transposeG g)
  let getStmts v = let ((stmts, cts), (PrefixName ps name), _) = f v in ((ps ++ [name]), stmts, cts)
  let allStmts = (map getStmts files) :: [(Prefix, FEnv, String)]
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
    emptyMod
--     (fname, [], M.empty, contents)
    allStmts'
  where
    depGraph :: [UserName] -> UserName -> String -> ExceptT SrcErr IO [FlatMod]
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
