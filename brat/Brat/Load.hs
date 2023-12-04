{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Brat.Load (loadFilename
                 ,loadFiles
                 ,parseFile
                 ,desugarEnv
                 ) where

import Brat.Checker.Clauses
import Brat.Checker.Helpers (ensureEmpty, wire)
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
import Util (duplicates,duplicatesWith)
import Bwd
import Control.Monad.Freer (req)

import Control.Exception (assert)
import Control.Monad.Except
import Data.Functor (($>))
import Data.List (sort)
import Data.List.HT (viewR)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Graph as G
import qualified Data.Map as M
import Data.Traversable (for)
import System.Directory (doesFileExist)
import System.FilePath

import Prelude hiding (last)

-- A Module is a node in the dependency graph
type FlatMod = ((FEnv, String) -- data at the node: declarations, and file contents
               ,Import -- name of this node
               ,[Import]) -- other nodes on which this depends

-- Result of checking/compiling a module
type VMod = (VEnv, [(UserName, VDecl)] -- all symbols from all modules
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
          [(_, Right ty@(VFun m@Braty ctx (ss :-> ts)))] -> (ty,) <$> let ?my = m in checkBody fnName verb (FV ctx ss ts)
          [(_, Right ty@(VFun m@Kerny ctx (ss :-> ts)))] -> (ty,) <$> let ?my = m in checkBody fnName verb (FV ctx ss ts)
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

loadStmtsWithEnv :: (VEnv, [(UserName, VDecl)]) -> (FilePath, Prefix, FEnv, String) -> Either SrcErr VMod
loadStmtsWithEnv (venv, oldDecls) (fname, pre, stmts, cts) = addSrcContext fname cts $ do
  -- hacky mess - cleanup!
  (decls, aliases) <- desugarEnv =<< elabEnv stmts
  -- Note the duplicates here works for anything Eq, but is O(n^2).
  -- TODO Since decl names can be ordered/hashed, we could be much faster.
  let (declNames, _) = unzip oldDecls
  let dups = duplicates (declNames ++ map (PrefixName pre . fnName) decls) in unless (null dups) $
    Left $ dumbErr $ NameClash $ show dups
  ((venv', vdecls), (holes, graph)) <- run venv root $ withAliases aliases $ do
    entries <- forM decls $ \d -> localFC (fnLoc d) $ do
      let name = PrefixName pre (fnName d)
      sig <- kindCheckRow (show name) (fnSig d)
      let (thing, ins) = case (fnLocality d) of
                          Local -> (Id, sig)
                          Extern sym -> (Prim sym, [])
      (_, unders, outs, _) <- next (show name) thing (B0, B0) ins sig
      pure ((name, d{fnSig=sig} :: VDecl), (unders, outs))
    -- We used to check there were no holes from that, but for now we do not bother
    let to_define = M.fromList [(name, unders) | ((name, _), (unders, _)) <- entries, (length unders) > 0]
    let vdecls = map fst entries
    -- Now generate environment mapping usernames to nodes in the graph
    let env = M.fromList [(name, overs) | ((name, _), (_, overs)) <- entries]
    localVEnv env $ do
      remaining <- foldM checkDecl' to_define vdecls
      pure $ assert (M.null remaining) -- all to_define were defined
    pure (env, vdecls)

  pure (venv <> venv', oldDecls <> vdecls, holes, [(PrefixName [] "main", graph)])
 where
  checkDecl' :: M.Map UserName [(Tgt, BinderType Brat)]
             -> (UserName, VDecl)
             -> Checking (M.Map UserName [(Tgt, BinderType Brat)])
  checkDecl' to_define (name, decl) =
    let (decl_defines, remaining) = M.updateLookupWithKey (\_ _ -> Nothing) name to_define
    in checkDecl pre decl decl_defines $> remaining

loadFilename :: [FilePath] -> String -> ExceptT SrcErr IO VMod
loadFilename libDirs file = do
  unless (takeExtension file == ".brat") $ fail $ "Filename " ++ file ++ " must end in .brat"
  let (path, fname) = splitFileName $ dropExtension file
  contents <- lift $ readFile file
  loadFiles (path :| libDirs) fname contents

-- Does not read the main file, but does read any imported files
loadFiles :: NonEmpty FilePath -> String -> String
         -> ExceptT SrcErr IO VMod
loadFiles (cwd :| extraDirs) fname contents = do
  let mainImport = Import { importName = dummyFC (plain fname)
                          , importQualified = True
                          , importAlias = Nothing
                          , importSelection = ImportAll }
  idx_mods <- M.elems <$> depGraph M.empty mainImport contents
  liftEither $ checkNoCycles idx_mods
  let (g, f, _) = G.graphFromEdges (map snd idx_mods)
  let files = G.topSort (G.transposeG g)
  -- Validate imports
  liftEither . addSrcContext fname contents $ forM_ files (validateImports . f)

  let allStmts = (getStmts . f) <$> files
  -- remove the prefix for the starting file
  allStmts' <- case viewR allStmts of
    -- the original file should be at the end of the allStmts list
    Just (rest, (_, mainPrf, mainStmts, mainCts)) -> do
      unless (mainPrf == [fname]) $
        throwError (SrcErr "" $ dumbErr (InternalError "Top of dependency graph wasn't main file"))
      deps <- for rest $ \(uname,b,c,d) -> findFile uname >>= pure . (,b,c,d)
      let main = (cwd </> fname ++ ".brat", [], mainStmts, mainCts)
      pure (deps ++ [main])
    Nothing -> throwError (SrcErr "" $ dumbErr (InternalError "Empty dependency graph"))
    -- keep (as we fold) and then return only the graphs from the last file in the list
  liftEither $ foldM
    (\(venv, decls, _, _) -> loadStmtsWithEnv (venv, decls))
    emptyMod
--     (fname, [], M.empty, contents)
    allStmts'
  where
    -- builds a map from Import to (index in which discovered, module)
    depGraph :: (M.Map Import (Int, FlatMod)) -- input map to which to add
             -> Import -> String
             -> ExceptT SrcErr IO (M.Map Import (Int, FlatMod))
    depGraph visited imp cts = let name = unWC (importName imp) in
      case M.lookup imp visited of
        Just _ -> pure visited
        Nothing -> do
          (imports, env) <- liftEither $ parseFile (nameToFile cwd name) cts
          let with_mod = M.insert imp (M.size visited,((env, cts), imp, imports)) visited
          foldM visit with_mod imports
     where
      visit :: M.Map Import (Int, FlatMod) -> Import -> ExceptT SrcErr IO (M.Map Import (Int, FlatMod))
      visit visited' imp' = do
        file <- findFile (unWC (importName imp'))
        cts <- lift $ readFile file
        depGraph visited' imp' cts

    getStmts :: ((FEnv, String), Import, [Import]) -> (UserName, Prefix, FEnv, String)
    getStmts (((decls, ts), cts), Import (WC _ pn@(PrefixName ps name)) qual alias sel, _) =
      let prefix = case (qual, alias) of (True, Nothing) -> ps ++ [name]
                                         (False, Nothing) -> []
                                         (_, Just chosenName) -> [unWC chosenName] in
      let p = case sel of ImportAll -> const True
                          ImportPartial ss -> (\d -> fnName d `elem` map unWC ss)
                          ImportHiding ss -> (\d -> fnName d `notElem` map unWC ss) in
      (pn, prefix, (filter p decls, ts), cts)

    -- Check that the names mentioned in the import actually exist and
    -- that aliases are unique
    validateImports :: ((FEnv, String), Import, [Import]) -> Either Error ()
    validateImports (((decls, _), _), Import name _ _ selection, imports) = do
      let names = case selection of ImportAll -> []
                                    ImportHiding ss -> ss
                                    ImportPartial ss -> ss
      forM_ names (\(WC fc s) -> if s `elem` (fnName <$> decls) then pure ()
                         else throwError $ Err (Just fc) (SymbolNotFound s (show name)))
      let aliases = foldr (\i as -> case importAlias i of Just a -> a:as
                                                          Nothing -> as) [] imports
      case duplicatesWith unWC aliases of
        (WC fc dupl:_) -> throwError $ Err (Just fc) (NameClash ("Alias not unique: " ++ show dupl))
        [] -> pure ()

    findFile :: UserName -> ExceptT SrcErr IO String
    findFile uname = let possibleLocations = [nameToFile dir uname | dir <- cwd:extraDirs] in
                       filterM (lift . doesFileExist) possibleLocations >>= \case
      [] -> throwError $ addSrcName (show uname) $ dumbErr (FileNotFound (show uname) possibleLocations)
      (x:_) -> pure x

    nameToFile :: FilePath -> UserName -> String
    nameToFile dir (PrefixName ps file) = dir </> (foldr (</>) file ps) ++ ".brat"

checkNoCycles :: [(Int, FlatMod)] -> Either SrcErr ()
checkNoCycles mods =
  let idxAndNames = [(i, unWC (importName n), unWC . importName <$> ns)
                    | (i, (_, n, ns)) <- mods]
      justName (_, n, _) = show n
  in case [verts | G.CyclicSCC verts <- G.stronglyConnCompR idxAndNames] of
    [] -> Right ()
    -- Report just the first SCC. Would be great to reduce to a single smallest cycle,
    -- but Data.Graph doesn't offer anything useful (e.g. Dijkstra's algorithm!)
    scc:_ -> Left $ let scc' = map justName (sort scc) -- sort by indices, then discard
                    in addSrcName (head scc') $ dumbErr $ ImportCycle scc'
