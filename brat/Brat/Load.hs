{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Brat.Load (loadFilename
                 ,loadFiles
                 ,parseFile
                 ,desugarEnv
                 ) where

import Brat.Checker.Clauses
import Brat.Checker.Helpers (ensureEmpty, wire)
import Brat.Checker.Monad
import Brat.Checker.Types (EnvData)
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
import Util (duplicates)
import Bwd
import Control.Monad.Freer (req)

import Control.Exception (assert)
import Control.Monad.Except
import Data.Functor ((<&>), ($>))
import Data.List (sort)
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

checkDecl :: Prefix -> VDecl -> Maybe [(Tgt, BinderType Brat)] -> Checking ()
checkDecl pre Decl{..} to_define = case (fnLocality, to_define) of
  (Local, Just decl_defines) -> localFC fnLoc $ do
    case fnBody of
      NoLhs body -> do
        (((), ()), ((), [])) <- let ?my = Braty in check body ((), decl_defines)
        pure ()
      -- TODO: Unify this with `getThunks` and `check (Th _)` code
      ThunkOf (WC _ verb) -> do
        (ty, box_out) <- case fnSig of
          -- Seems like it should be important to not drop the context here
          [(_, Right ty@(VFun m@Braty ctx (ss :-> ts)))] -> (ty,) <$> let ?my = m in checkBody fnName verb (ctx, ss, ts)
          [(_, Right ty@(VFun m@Kerny ctx (ss :-> ts)))] -> (ty,) <$> let ?my = m in checkBody fnName verb (ctx, ss, ts)
          [u] -> req $ Throw (dumbErr $ ExpectedThunk "" (show u))
          [] -> err $ EmptyRow name
          (_:_) -> err $ MultipleOutputsForThunk name
        let [(thunk_in, _)] = decl_defines
        wire (box_out, ty, thunk_in)
      Undefined -> error "No body in `checkDecl`"
    pure ()
  (Extern _, Nothing) -> pure () -- no body to check; all sigs kindCheck'd already
 where
  uname = PrefixName pre fnName
  name = show uname

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
  -- Note the duplicates here works for anything Eq, but is O(n^2).
  -- TODO Since decl names can be ordered/hashed, we could be much faster.
  let dups = duplicates (map fnName decls) in unless (null dups) $
    Left $ dumbErr $ NameClash $ show dups
  -- kindCheck the declaration signatures, but throw away the graph
  (vdecls, (holes, _graph)) <- run venv root $ withAliases aliases $ forM decls $ \d ->
    kindCheckRow (fnSig d) <&> \sig -> (d{fnSig=sig} :: VDecl)
  unless (length holes == 0) $ Left $ dumbErr $ InternalError "Decl sigs generated holes"
  
  (venv', (holes, graph)) <- run venv root $ withAliases aliases $ do
      -- Generate environment mapping usernames to nodes in the graph
      entries <- mapM declNode vdecls
      let env = M.fromList [(name, overs) | (name, _, overs) <- entries]
      localVEnv env $ do
        let to_define = M.fromList [(name, unders) | (name, unders, _) <- entries, (length unders) > 0]
        remaining <- foldM checkDecl' to_define vdecls
        pure $ assert (M.null remaining) -- all to_define were defined
      pure env

  pure (venv <> venv', oldDecls <> vdecls, holes, [(PrefixName [] "main", graph)])
 where
  declNode :: VDecl -> Checking (UserName, [(Tgt, BinderType Brat)], EnvData Brat)
  declNode Decl{..} = let
      name = PrefixName pre fnName
      (ins, thing) = case fnLocality of
        Local -> (fnSig, Id) -- Compilation will probably want these to be flagged with the name
        Extern sym -> ([], Prim sym)
      in next (show name) thing (B0, B0) ins fnSig <&> (\(_, unders, outs, _) -> (name, unders,outs))

  checkDecl' :: M.Map UserName [(Tgt, BinderType Brat)]
             -> VDecl
             -> Checking (M.Map UserName [(Tgt, BinderType Brat)])
  checkDecl' to_define decl@Decl{fnName=fnName} =
    let name = PrefixName pre fnName
        (decl_defines, remaining) = M.updateLookupWithKey (\_ _ -> Nothing) name to_define
    in checkDecl pre decl decl_defines $> remaining

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
  idx_mods <- map snd <$> M.toList <$> depGraph M.empty fn contents
  liftEither $ checkNoCycles idx_mods
  let (g, f, _) = G.graphFromEdges (map snd idx_mods) -- discard indices

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
    -- builds a map from username to (index in which discovered, module)
    depGraph :: (M.Map UserName (Int, FlatMod)) -- input map to which to add
             -> UserName -> String
             -> ExceptT SrcErr IO (M.Map UserName (Int, FlatMod))
    depGraph visited name cts = case M.lookup name visited of
      Just _ -> pure visited
      Nothing -> do
        (imports, env) <- liftEither $ parseFile (nameToFile name) cts
        let with_mod = M.insert name (M.size visited,((env, cts), name, imports)) visited
        foldM visit with_mod imports
     where
      visit visited' name' = do
        let file = nameToFile name'
        exists <- lift $ doesFileExist file
        unless exists $
          throwError $ addSrcName file $ dumbErr (FileNotFound file)
        cts <- lift $ readFile file
        depGraph visited' name' cts

    nameToFile :: UserName -> String
    nameToFile (PrefixName ps file) = path </> (foldr (</>) file ps) ++ ".brat"

checkNoCycles :: [(Int, FlatMod)] -> Either SrcErr ()
checkNoCycles mods =
  let idxAndNames = [(i, n, ns) | (i, (_, n, ns)) <- mods]
      justName (_, n, _) = show n
  in case [verts | G.CyclicSCC verts <- G.stronglyConnCompR idxAndNames] of
    [] -> Right ()
    -- Report just the first SCC. Would be great to reduce to a single smallest cycle,
    -- but Data.Graph doesn't offer anything useful (e.g. Dijkstra's algorithm!)
    scc:_ -> Left $ let scc' = map justName (sort scc) -- sort by indices, then discard
                    in addSrcName (head scc') $ dumbErr $ ImportCycle scc'
