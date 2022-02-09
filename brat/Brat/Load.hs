module Brat.Load (loadFile, loadFileWithEnv, LoadType(..), typeGraph) where

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
import Control.Monad.Freer (req)
import Util

import Control.Monad (unless, when)
import Data.Functor  (($>))
import Data.List.NonEmpty (nonEmpty)
import Debug.Trace

data LoadType = Lib | Exe deriving (Eq, Show)

addNounsToEnv :: [NDecl] -> VEnv
addNounsToEnv = aux root
 where
  aux :: Namespace -> [NDecl] -> VEnv
  aux _ [] = []
  aux (MkName ns, _) (Decl{..}:decls) =
    let freshName = MkName ((fnName, 0) : ns)
        venv = [ (fnName, ((freshName, port), ty)) | (port, ty) <- fnSig]
    in  venv <> aux (freshName, 0) decls

addVerbsToEnv :: [VDecl] -> CEnv
addVerbsToEnv = foldr (\d cenv -> (fnName d, fnSig d):cenv) []

checkVerb :: VDecl -> Checking ((), Connectors Brat Chk Verb)
checkVerb Decl{..}
  | Local <- fnLocality = do
  let (ss :-> ts) = fnSig
  src <- next (fnName <> "/in") Source ss ss
  tgt <- next (fnName <> "/out") Target ts ts
  let thunkTy = ("value", C (ss :-> ts))
  thunk <- next (fnName ++ "_thunk") (src :>>: tgt) [] [thunkTy]
  eval  <- next ("Eval(" ++ fnName ++ ")") (Eval (thunk, "value")) (thunkTy:ss) ts
  wire ((thunk, "value"), Right (snd thunkTy), (eval, "value"))
  wrapError (addSrc fnName) $
    checkClauses fnBody ([((src, port), ty) | (port, ty) <- ss]
                        ,[((tgt, port), ty) | (port, ty) <- ts])
  | Extern sym <- fnLocality = do
      let (ss :-> ts) = fnSig
      next fnName (Prim sym) ss ts
      pure ((), ([], []))

checkNoun :: NDecl -> Checking ()
checkNoun Decl{..}
  | Local <- fnLocality = do
  tgt <- next fnName Id fnSig fnSig
  let NounBody body = fnBody
  wrapError (addSrc fnName) $
    (check body ((), [((tgt, port), ty) | (port, ty) <- fnSig]))
  pure ()
  | Extern sym <- fnLocality = () <$ next fnName (Prim sym) [] fnSig

typeGraph :: (CEnv, VEnv) -> NDecl -> Either Error Graph
typeGraph (cenv, venv) fn = do
  (_, (_, g)) <- run (cenv, venv, [], [], fnLoc fn) (checkNoun fn)
  pure g

loadFileWithEnv :: (CEnv, VEnv, [NDecl],[VDecl]) -> LoadType -> String -> String
                -> Either Error (CEnv, VEnv, [NDecl], [VDecl], [TypedHole], Graph)
loadFileWithEnv (cenv, venv, nouns, verbs) loadType fname contents = do
  (fnouns, fverbs) <- desugarEnv =<< parseFile fname contents
  nouns <- pure (fnouns ++ nouns)
  verbs <- pure (fverbs ++ verbs)
  -- hacky mess - cleanup!
  unless (null (duplicates nouns)) $
    Left . Err Nothing Nothing . NameClash $ show (duplicates nouns)
  unless (null (duplicates verbs)) $
    Left . Err Nothing Nothing . NameClash $ show (duplicates verbs)
  cenv <- pure $ cenv <> addVerbsToEnv verbs
  venv <- pure $ venv <> addNounsToEnv nouns
  -- giving a dummy file context - not ideal
  let env = (cenv, venv, nouns, verbs, FC (Pos 0 0) (Pos 0 0))
  (_, (holes, graph))   <- run env (mapM (\d -> localFC (fnLoc d) $ checkNoun d) nouns)
  (_, (holes', graph')) <- run env (mapM (\d -> localFC (fnLoc d) $ checkVerb d) verbs)

  -- all good? Let's just get the graph for `main` (and assume it's a noun)
  when (loadType == Exe) $ do
    main <- maybeToRight (Err Nothing Nothing MainNotFound) $ lookupBy ((=="main") . fnName) id nouns
    (_, (_, mgraph)) <- run env (checkNoun main)
    traceM "-----------------"
    traceM (dot $ mgraph)
    traceM "------------------"
    traceM (show $ mgraph)
    traceM "-------------------"
    traceM (let [(_, K ss ts)] = fnSig main in show . flip compileCircuit (ss,ts) $ mgraph)
    traceM "--------------------"

  pure (cenv, venv, nouns, verbs, holes ++ holes', graph <> graph')

loadFile :: LoadType -> String -> String
         -> Either Error (CEnv, VEnv, [NDecl], [VDecl], [TypedHole], Graph)
loadFile = loadFileWithEnv ([], [], [], [])
