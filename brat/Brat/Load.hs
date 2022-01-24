module Brat.Load (loadFile, loadFileWithEnv) where

import Brat.Checker
import Brat.Dot
import Brat.Error
import Brat.FC
import Brat.Naming
import Brat.Parser
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.Raw
import Control.Monad.Freer (req)
import Util

import Control.Monad (unless)
import Data.List (intersect)
import Data.List.NonEmpty (nonEmpty)
import Debug.Trace

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
checkVerb Decl{..} = do
  src <- req $ Fresh "above"
  tgt <- req $ Fresh "below"
  let (ss :-> ts) = fnSig
  case nonEmpty fnBody of
    Nothing -> fail $ "No body found for " ++ fnName
    Just body -> wrapError (addSrc fnName) $
      checkClauses body ([((src, port), ty) | (port, ty) <- ss]
                        ,[((tgt, port), ty) | (port, ty) <- ts])

checkNoun :: NDecl -> Checking ()
checkNoun Decl{..} = do
  tgt <- req $ Fresh "hypothesis"
  let [NounBody body] = fnBody
  wrapError (addSrc fnName) $
    (check body ((), [((tgt, port), ty) | (port, ty) <- fnSig]))
  pure ()

loadFileWithEnv :: ([NDecl],[VDecl]) -> String -> String
                -> Either Error ([NDecl], [VDecl], [TypedHole])
loadFileWithEnv (nouns, verbs) fname contents = do
  (fnouns, fverbs) <- desugarEnv =<< parseFile fname contents
  nouns <- pure (fnouns ++ nouns)
  verbs <- pure (fverbs ++ verbs)
  -- hacky mess - cleanup!
  unless (null (duplicates nouns)) $
    Left . Err Nothing Nothing . NameClash $ show (duplicates nouns)
  unless (null (duplicates verbs)) $
    Left . Err Nothing Nothing . NameClash $ show (duplicates verbs)
  let cenv = addVerbsToEnv verbs
  let venv = addNounsToEnv nouns
  -- giving a dummy file context - not ideal
  let env = (cenv, venv, nouns, verbs, FC (Pos 0 0) (Pos 0 0))
  (_, (holes, graph))   <- run env (mapM checkNoun (filter (not . null . fnBody) nouns))
  (_, (holes', graph')) <- run env (mapM checkVerb (filter (not . null . fnBody) verbs))

  traceM "----------------"
  traceM (dot $ graph <> graph')
  traceM "----------------"
  pure (nouns, verbs, holes ++ holes')

loadFile :: String -> String -> Either Error ([NDecl], [VDecl], [TypedHole])
loadFile = loadFileWithEnv ([], [])
