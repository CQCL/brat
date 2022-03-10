module Brat.Load (emptyMod
                 ,loadFile
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
type Mod = (CEnv, VEnv, [NDecl], [VDecl], [TypedHole], Graph)
data LoadType = Lib | Exe deriving (Eq, Show)

emptyMod :: Mod
emptyMod = ([], [], [], [], [], ([], []))

addNounsToEnv :: Prefix -> [NDecl] -> VEnv
addNounsToEnv pre = aux root
 where
  aux :: Namespace -> [NDecl] -> VEnv
  aux _ [] = []
  aux (MkName ns, _) (Decl{..}:decls) =
    let freshName = MkName ((fnName, 0) : ns)
        venv = [ (PrefixName pre fnName, ((freshName, port), ty)) | (port, ty) <- fnSig]
    in  venv <> aux (freshName, 0) decls

addVerbsToEnv :: Prefix -> [VDecl] -> CEnv
addVerbsToEnv pre = foldr (\d cenv -> (PrefixName pre (fnName d), fnSig d):cenv) []

checkVerb :: Prefix -> VDecl -> Checking ((), Connectors Brat Chk Verb)
checkVerb pre Decl{..}
  = withPrefix fnName $
    case fnLocality of
      Local -> do
        let (ss :-> ts) = fnSig
        src <- next (name <> "/in") Source ss ss
        tgt <- next (name <> "/out") Target ts ts
        let thunkTy = ("value", C (ss :-> ts))
        thunk <- next (name ++ "_thunk") (src :>>: tgt) [] [thunkTy]
        eval  <- next ("Eval(" ++ name ++ ")") (Eval (thunk, "value")) (thunkTy:ss) ts
        wire ((thunk, "value"), Right (snd thunkTy), (eval, "value"))
        wrapError (addSrc name) $
          checkClauses fnBody ([((src, port), ty) | (port, ty) <- ss]
                              ,[((tgt, port), ty) | (port, ty) <- ts])
      Extern sym -> do
        let (ss :-> ts) = fnSig
        next name (Prim sym) ss ts
        pure ((), ([], []))
 where
  name = show $ PrefixName pre fnName
checkNoun :: Prefix -> NDecl -> Checking ()
checkNoun pre Decl{..}
  | Local <- fnLocality = do
  tgt <- next fnName Id fnSig fnSig
  let NounBody body = fnBody
  wrapError (addSrc fnName) $
    (check body ((), [((tgt, port), ty) | (port, ty) <- fnSig]))
  pure ()
  | Extern sym <- fnLocality = () <$ next (show $ PrefixName pre fnName) (Prim sym) [] fnSig

typeGraph :: (CEnv, VEnv) -> NDecl -> Either Error Graph
typeGraph (cenv, venv) fn = do
  (_, (_, g)) <- run (cenv, venv, [], [], fnLoc fn) (checkNoun [] fn)
  pure g

loadStmtsWithEnv :: Mod -> Prefix -> LoadType -> RawEnv -> Either Error Mod
loadStmtsWithEnv e@(cenv, venv, nouns, verbs, holes, graph) pre loadType stmts = do
  (fnouns, fverbs) <- desugarEnv stmts
  nouns <- pure (fnouns ++ nouns)
  verbs <- pure (fverbs ++ verbs)
  -- hacky mess - cleanup!
  unless (null (duplicates nouns)) $
    Left . Err Nothing Nothing . NameClash $ show (duplicates nouns)
  unless (null (duplicates verbs)) $
    Left . Err Nothing Nothing . NameClash $ show (duplicates verbs)
  cenv <- pure $ cenv <> addVerbsToEnv pre verbs
  venv <- pure $ venv <> addNounsToEnv pre nouns
  -- giving a dummy file context - not ideal
  let env = (cenv, venv, nouns, verbs, FC (Pos 0 0) (Pos 0 0))
  (_, (holes, graph))   <- run env (mapM (\d -> localFC (fnLoc d) $ checkNoun pre d) nouns)
  (_, (holes', graph')) <- run env (mapM (\d -> localFC (fnLoc d) $ checkVerb pre d) verbs)

  -- all good? Let's just get the graph for `main` (and assume it's a noun)
  when (loadType == Exe) $ do
    main <- maybeToRight (Err Nothing Nothing MainNotFound) $ lookupBy ((=="main") . fnName) id nouns
    (_, (_, mgraph)) <- run env (checkNoun [] main)
    pure ()

  pure (cenv, venv, nouns, verbs, holes ++ holes', graph <> graph')

loadFile :: LoadType -> FilePath -> String -> String
         -> ExceptT Error IO Mod
loadFile lt path fname contents = do
  let fn = plain fname
  cts <- if contents == ""
         then lift $ readFile (nameToFile fn)
         else return contents
  edges <- depGraph [] fn cts

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
          cts <- lift $ readFile (nameToFile name')
          depGraph (name:chain) name' cts
        pure ((env, name, imports):(concat es))

    nameToFile :: UserName -> String
    nameToFile (PrefixName ps file) = path </> (foldr (</>) file ps) ++ ".brat"
