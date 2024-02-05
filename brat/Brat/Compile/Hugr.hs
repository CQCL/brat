{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module Brat.Compile.Hugr (compile) where

import Brat.Checker.Types (VEnv)
import Brat.Graph
import Brat.Naming hiding (fresh)
import Brat.Syntax.Port
import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.UserName
import Data.Hugr.Ops
import Data.Hugr.Types
import Hasochism

import Data.Aeson
import qualified Data.ByteString.Lazy as BS
import Data.Foldable (traverse_)
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import Data.Text
import Data.Type.Equality ((:~:)(..))
import Control.Monad.State

{-
For each top level function definition in BRAT: we should have a FuncDef node in
hugr, whose child graph is the body of the function

Inspections of arguments should map
-}

type NodeId = Int

type PortId = (NodeId -- Which node
              ,Int    -- which port on that node
              )

data CompilationState = CompilationState
 { nameSupply :: Int
 , nodes :: [(Int, HugrOp)]
 , edges :: [(PortId, PortId)]
 , roots :: [NodeId]
 , sources :: [NodeId]
 , targets :: [NodeId]
 , mapping :: M.Map Name Int
 }

emptyCS = CompilationState 0 [] [] [] [] [] M.empty

fresh :: Compile Int
fresh = do
  st <- get
  let n = nameSupply st
  put (st { nameSupply = n + 1 })
  pure n

addEdge :: (PortId, PortId) -> Compile ()
addEdge e = do
  st <- get
  let es = edges st
  put (st { edges = e:es })

data HugrOp
  = OpIn InputNode
  | OpOut OutputNode
  | OpDefn FuncDefn

instance ToJSON HugrOp where
  toJSON (OpIn op) = toJSON op
  toJSON (OpOut op) = toJSON op
  toJSON (OpDefn op) = toJSON op

data Hugr = Hugr
  { hugr_nodes :: [HugrOp]
  , hugr_edges :: [(PortId, PortId)]
  }

instance ToJSON Hugr where
  toJSON (Hugr ns es) = object ["version" .= ("v0" :: Text)
                               ,"nodes" .= ns
                               ,"edges" .= es
                               ]

type Compile = State CompilationState

compileFunctions :: VEnv -> [(UserName, Graph)] -> Compile ()
compileFunctions venv stuff =
  traverse_ (\(name, g) -> compileFunction name (getFunctionType name) g) stuff
 where
  getFunctionType :: UserName -> CTy Kernel Z
  getFunctionType name = case M.lookup name venv of
    Just [(_, Right (VFun Kerny cty))] -> cty
    Nothing -> error $ show name ++ " isn't a function"

-- Make a FuncDef node and call compileDFG with that as the parent
compileFunction :: UserName -> CTy Kernel Z -> Graph -> Compile ()
compileFunction name sig g = do
  funcDefnId <- fresh
  -- Being it's own parent means it's at the top level(?)
  let funcDefn = FuncDefn funcDefnId (show name) (compileSig sig)
  st <- get
  put (st { roots = funcDefnId : roots st
          , nodes = (funcDefnId, OpDefn funcDefn) : nodes st
          })
  compileDFG funcDefnId g

compileSig :: CTy Kernel Z -> PolyFuncType
compileSig (ss :->> ts) = case (kernelNoBind ss, kernelNoBind ts) of
  (Refl, Refl) -> PolyFuncType []
                  (FunctionType (compileRo ss) (compileRo ts))
 where
  compileRo :: Ro Kernel Z Z -> [HugrType]
  compileRo R0 = []
  compileRo (RPr (_, ty) ro) = compileType ty : compileRo ro

compileType :: SVal Z -> HugrType
compileType VQ = HTQubit

todo = undefined

mkInput :: NodeId -> [(PortName, SVal Z)] -> Compile NodeId
mkInput parent tys = do
  tys <- pure $ compileType . snd <$> tys
  this <- fresh
  let node = OpIn (InputNode parent tys)
  st <- get
  put (st { nodes = (this, node):nodes st, sources = this:sources st })
  pure this

mkOutput :: NodeId -> [(PortName, SVal Z)] -> Compile NodeId
mkOutput parent tys = do
  tys <- pure $ compileType . snd <$> tys
  this <- fresh
  let node = OpOut (OutputNode parent tys)
  st <- get
  put (st { nodes = (this, node):nodes st, targets = this:targets st })
  pure this

compileNodes :: NodeId -> M.Map Name Node -> Compile (M.Map Name (Maybe NodeId))
compileNodes parent = traverse aux
 where
  -- If we only care about the node for typechecking, then drop it and return
  -- `Nothing` instead of a NodeId
  aux :: Node -> Compile (Maybe NodeId)
  aux (BratNode _ _ _) = pure Nothing
  aux (KernelNode thing ins outs) = do
    case thing of
      Prim _ -> todo
      Const tm -> todo
      Eval outPort -> todo
      (src :>>: tgt) -> todo
      Source -> Just <$> mkInput parent outs
      Target -> Just <$> mkOutput parent ins
      Id -> pure Nothing
      Hypo -> pure Nothing
      Constructor c -> todo
      Selector c -> todo
      ArithNode op -> todo


compileDFG :: Int -> Graph -> Compile ()
compileDFG parent (nodes, wires) = do
  mapping <- compileNodes parent nodes
  let es = convertWire mapping <$> wires
  traverse_ addEdge (catMaybes es)
 where
  -- If we dropped a node in compile nodes, drop all wires that connect to it
  convertWire :: M.Map Name (Maybe Int) -> Wire -> Maybe (PortId, PortId)
  convertWire mapping (Ex src srcPort, _, In tgt tgtPort) = do
    src <- mapping M.! src
    tgt <- mapping M.! tgt
    -- Port offsets should be the same in both graphs
    pure ((src, srcPort), (tgt, tgtPort))

dumpJSON :: Compile BS.ByteString
dumpJSON = do
  st <- get
  -- let first = roots st ++ inputs st ++ outputs st
  -- let rest = filter (`elem` done) (nodes st)
  pure $ encode (Hugr (snd <$> nodes st) (edges st))

compile :: VEnv -> [(UserName, Graph)] -> BS.ByteString
compile venv gs = evalState
                  (compileFunctions venv gs *> dumpJSON)
                  emptyCS
