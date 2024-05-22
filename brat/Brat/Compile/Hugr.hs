-- TODO: Remove DFG children of case nodes. Case nodes have inputs and outputs, so they *are* the DFG
-- possibly we need to be smart about compiling DFGs for this
-- they're getting the boxes as arguments

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Brat.Compile.Hugr (compile) where

import Brat.Constructors (pattern CFalse, pattern CTrue)
import Brat.Checker.Monad (track, trackM, CheckingSig(..))
import Brat.Checker.Helpers (binderToValue)
import Brat.Checker.Types (EndType(..), Store(..), VEnv)
import Brat.Eval (eval, kindType)
import Brat.Graph hiding (lookupNode)
import Brat.Naming
import Brat.Syntax.Port
import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Control.Monad.Freer
import Data.Hugr.Ops
import Data.Hugr.Types
import Hasochism

import Control.Exception (assert)
import Control.Monad (unless)
import Data.Aeson
import Data.Bifunctor (second)
import qualified Data.ByteString.Lazy as BS
import Data.Foldable (traverse_, for_)
import Data.Functor ((<&>), ($>))
import Data.List (partition, sort, sortBy)
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust)
import Data.Ord (comparing)
import Data.Traversable (for)
import Data.Tuple.HT (fst3)
import Control.Monad.State
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import GHC.Base (NonEmpty(..))
import Brat.Syntax.Simple (SimpleTerm)

{-
For each top level function definition or value in BRAT: we should have a FuncDef node in
hugr, whose child graph is the body of the function
-}

newtype NodeId = NodeId Name deriving (Eq, Ord, Show)

type TypedPort = (PortId NodeId, HugrType)

data CompilationState = CompilationState
 { bratGraph :: Graph -- the input BRAT Graph; should not be written
 , nameSupply :: Namespace
 , nodes :: [(HugrOp NodeId, NodeId)] -- the two NodeIds are the type of the parent pointer, and the id of this node
 , edges :: [(PortId NodeId, PortId NodeId)]
 , compiled :: M.Map Name NodeId  -- Mapping from Brat nodes to Hugr nodes
 , holes :: Bwd Name -- for Kernel graphs, list of Splices found in order
 , store :: Store -- Kinds and values of global variables, for compiling types
 -- A map from Id nodes representing functions and values in the brat graph,
 -- to the FuncDef nodes that we create for them. The bool, if true, says that
 -- we must insert an *extra* call, beyond what's required in Brat, to compute the value
 -- of the decl (e.g. `x :: Int` `x = 1+2` requires calling the FuncDefn to calculate 1+2).
 -- Note that in the future this could be extended to allow top-level Consts too.
 , decls :: M.Map Name (NodeId, Bool)
 }

emptyCS g ns store = CompilationState
  { bratGraph = g
  , nameSupply = ns
  , nodes = []
  , edges = []
  , compiled = M.empty
  , holes = B0
  , store = store
  , decls = M.empty
  }

registerFuncDef :: Name -> (NodeId, Bool) -> Compile ()
registerFuncDef name hugrDef = do
  st <- get
  put (st { decls = M.insert name hugrDef (decls st) })


freshNode :: String -> Compile NodeId
freshNode str = do
  st <- get
  let ns = nameSupply st
  let (freshName, newSupply) = fresh str ns
  put (st { nameSupply = newSupply })
  pure (NodeId freshName)

addEdge :: (PortId NodeId, PortId NodeId) -> Compile ()
addEdge e = do
  st <- get
  let es = edges st
  put (st { edges = e:es })

addNode :: String -> HugrOp NodeId -> Compile NodeId
addNode name op = do
  id <- freshNode name
  st <- get
  put (st { nodes = (op, id) : nodes st })
  pure id


type Compile = State CompilationState

instance FreshMonad Compile where
  freshName x = do
    s <- get
    let (name, newSupply) = fresh x (nameSupply s)
    put (s { nameSupply = newSupply })
    pure name

  x -! c = do
    s <- get
    let (nsx, nsNew) = split x (nameSupply s)
    put (s { nameSupply = nsx })
    v <- c
    put (s { nameSupply = nsNew })
    pure v


runCheckingInCompile :: Free CheckingSig t -> Compile t
runCheckingInCompile (Ret t) = pure t
runCheckingInCompile (Req (ELup e) k) = do
  emap <- gets (valueMap . store)
  runCheckingInCompile (k (M.lookup e emap))
runCheckingInCompile (Req _ _) = error $ "Compile monad found a command it can't handle"

compileSig :: CTy m Z -> Compile PolyFuncType
compileSig cty = PolyFuncType [] <$> compileSigWorker [] 0 cty

compileSigWorker :: [Maybe HugrType] -> Int -> CTy m Z -> Compile FunctionType
compileSigWorker hts lvl (ss :->> ts) = do
  (inRo, hts, acc) <- compileRo hts (lvl, S0) ss
  (outRo, _, _) <- compileRo hts acc ts
  pure $ FunctionType inRo outRo

compileRo :: forall m i j
           . [Maybe HugrType] -- The binders that we've gone under
          -> (Int, Valz i)    -- Next de Bruijn level, and context for evaluation
          -> Ro m i j -- The Ro that we're processing
          -> Compile ([HugrType]       -- The hugr type of the row
                     ,[Maybe HugrType] -- Things to instantiate our de Bruijn levels in
                     ,(Int, Valz j)
                     )
compileRo hts acc R0 = pure ([], hts, acc)
compileRo hts (lvl, stk) (RPr (_, ty) ro) = do
  ty <- runCheckingInCompile (eval stk ty) >>= compileTypeWorker hts lvl
  (tys, hts, stuff) <- compileRo hts (lvl, stk) ro
  pure (ty:tys, hts, stuff)
compileRo hts (lvl, stk) (REx (_, k) (ga ::- ro)) = do
  ty <- compileTypeWorker hts lvl (kindType k)
  (tys, hts, acc) <- compileRo (hts ++ [stashKind k]) (lvl + 1, stk <<+ ga :<< VApp (VLvl lvl k) B0) ro
  pure (ty:tys, hts, acc)
 where
  -- What to substitute a de Bruijn reference to this argument for
  stashKind :: TypeKind -> Maybe HugrType
  stashKind Nat = Nothing -- We only expect to lookup types in compileType, not #
  stashKind (TypeFor _ _) = Just (HTTuple []) -- Star and dollar become unit type

-- Val Z should already be eval'd at this point
compileTypeWorker :: [(Maybe HugrType)]
            -> Int -- The next de Bruijn level, for calling compileRo
            -> Val Z
            -> Compile HugrType
compileTypeWorker _ _ TQ = pure HTQubit
compileTypeWorker _ _ TMoney = pure HTQubit
compileTypeWorker _ _ TBit = pure $ HTSum (SU (UnitSum 2))
compileTypeWorker _ _ TBool = pure $ HTSum (SU (UnitSum 2))
compileTypeWorker _ _ TInt = pure hugrInt
compileTypeWorker _ _ TNat = pure hugrInt
compileTypeWorker _ _ TFloat = pure hugrFloat
compileTypeWorker hts lvl ty@(TCons _ _) = HTTuple <$> (tuple ty)
 where
  tuple :: Val Z -> Compile [HugrType]
  tuple (TCons hd rest) = (:) <$> compileTypeWorker hts lvl hd <*> tuple rest
  tuple TNil = pure []
  tuple ty = error $ "Found " ++ show ty  ++ " in supposed tuple type"
compileTypeWorker _ _ TNil = pure $ HTTuple []
compileTypeWorker hts lvl (VSum my ros) = case my of
  Braty -> error "Todo: compileTypeWorker for BRAT"
  Kerny -> do
    ros <- traverse (\(Some (Flip ro)) -> fst3 <$> (compileRo hts (lvl, S0) ro)) ros
    pure $ HTSum (SG (GeneralSum (HTTuple <$> ros)))
compileTypeWorker hts lvl (TVec el _) = hugrList <$> (compileTypeWorker hts lvl el)
compileTypeWorker tys _ (VApp (VLvl i _) _) = case tys !! i of
                                           Nothing -> error "Can't resolve reference to type variable"
                                           Just ty -> pure ty
compileTypeWorker _ _ (VApp (VPar e) _) = gets ((M.! e) . typeMap . store) >>= \case
  -- We're not doing anything special for higher order kinds
  EndType Braty (Left (TypeFor _ _)) -> do
    res <- gets (M.lookup e . valueMap . store)
    res <- traverse compileType res
    pure $ fromMaybe (HTTuple []) res
  EndType Braty ty -> error $ "Trying to compile ill-kinded type (" ++ show ty ++ ")"
  EndType Kerny ty -> error $ "Trying to compile ill-kinded type (" ++ show ty ++ ")"

compileTypeWorker hts lvl (VFun _ cty) = do
  fun_ty <- compileSigWorker hts lvl cty
  pure . HTFunc $ PolyFuncType [] fun_ty
compileTypeWorker _ _ ty = error $ "todo: compile type " ++ show ty

compileType :: Val Z -> Compile HugrType
compileType = compileTypeWorker [] 0

addOp :: HugrOp NodeId -> NodeId -> Compile ()
addOp op name | track ("addOp " ++ show op ++ show name) False = undefined
addOp op name = do
  st <- get
  put (st { nodes = (op, name):nodes st })

registerCompiled :: Name -> NodeId -> Compile ()
registerCompiled from to | track (show from ++ " |-> " ++ show to) False = undefined
registerCompiled from to = do
  st <- get
  put (st { compiled = M.insert from to (compiled st) })

compileConst :: NodeId -> SimpleTerm -> Val Z -> Compile NodeId
compileConst parent tm ty = do
  ty <- compileType ty
  constId <- addNode "Const" (OpConst (ConstOp parent (constFromSimple tm) ty))
  loadId <- addNode "LoadConst" (OpLoadConstant (LoadConstantOp parent ty))
  addEdge (Port constId 0, Port loadId 0)
  pure loadId

compileArithNode :: NodeId -> ArithOp -> Val Z -> Compile NodeId
compileArithNode parent op TNat  = addNode (show op ++ "_Nat") $ OpCustom $ case op of
  Add -> binaryIntOp parent "iadd"
  Sub -> binaryIntOp parent "isub"
  Mul-> binaryIntOp parent "imul"
  Div -> intOp parent "idiv_u" (FunctionType [hugrInt, hugrInt] [hugrInt]) [TANat intWidth, TANat intWidth]
  Pow -> error "TODO: Pow"  -- Not defined in extension
compileArithNode parent op TInt  = addNode (show op ++ "_Int") $ OpCustom $ case op of
  Add -> binaryIntOp parent "iadd"
  Sub -> binaryIntOp parent "isub"
  Mul-> binaryIntOp parent "imul"
  Div -> intOp parent "idiv_u" (FunctionType [hugrInt, hugrInt] [hugrInt]) [TANat intWidth, TANat intWidth]
  Pow -> error "TODO: Pow"  -- Not defined in extension
compileArithNode parent op TFloat  = addNode (show op ++ "_Float") $ OpCustom $ case op of
  Add -> binaryFloatOp parent "fadd"
  Sub -> binaryFloatOp parent "fsub"
  Mul-> binaryFloatOp parent "fmul"
  Div-> binaryFloatOp parent "fdiv"
  Pow -> error "TODO: Pow"  -- Not defined in extension
compileArithNode _ _ ty = error $ "compileArithNode: Unexpected type " ++ show ty

-- Parent had better be a FuncDef
compileFunClauses :: [HugrType] -> NonEmpty (TestMatchData m, Name) -> NodeId -> Compile ()
compileFunClauses ins cs parent = do
  inputNode <- addNode ("FunClauses.Input") (OpIn (InputNode parent ins))
  ccOuts <- compileClauses parent (zip (Port inputNode <$> [0..]) ins) cs
  addNodeWithInputs "FunClauses.Output" (OpOut (OutputNode parent (snd <$> ccOuts))) ccOuts []
  pure ()

renameAndSortHugr :: [(HugrOp NodeId, NodeId)] -> [(PortId NodeId, PortId NodeId)] -> Hugr Int
renameAndSortHugr nodes edges  = fmap update (Hugr (fst <$> sorted_nodes) edges) where
  sorted_nodes = let ([root], rest) = partition (\(n, nid) -> nid == getParent n) nodes in
                   root : sort rest

  names2Pos = M.fromList $ zip (snd <$> sorted_nodes) ([0..] :: [Int])

  update :: NodeId -> Int
  update name = case M.lookup name names2Pos of
                  Just ans -> ans
                  Nothing -> error ("Couldn't find node " ++ show name ++ "???")


dumpJSON :: Compile BS.ByteString
dumpJSON = do
  ns <- gets nodes
  es <- gets edges
  pure $ encode (renameAndSortHugr ns es)

compileClauses :: NodeId -> [TypedPort] -> NonEmpty (TestMatchData m, Name) -> Compile [TypedPort]
compileClauses parent ins ((matchData, rhs) :| clauses) = do
  (ns, _) <- gets bratGraph
  -- RHS has to be a box, so it must have a function type
  outTys <- case nodeOuts (ns M.! rhs) of
    [(_, VFun _ cty)] -> (body <$> compileSig cty) >>= \(FunctionType _ outs) -> pure outs
    _ -> error "Expected 1 kernel function type from rhs"

  -- Compile the match: testResult is the port holding the dynamic match result
  -- with the type `sumTy`
  let TestMatchData my matchSeq = matchData
  matchSeq <- traverse (compileBinderTy my) matchSeq

  let portTbl = zip (fst <$> matchInputs matchSeq) ins
  testResult <- compileMatchSequence parent portTbl matchSeq

  -- Feed the test result into a conditional
  makeConditional parent testResult [] [("didntMatch", didntMatch outTys)
                                       ,("didMatch", didMatch outTys)
                                       ]
 where
  didntMatch :: [HugrType] -> NodeId -> [TypedPort] -> Compile [TypedPort]
  didntMatch outTys parent ins = case nonEmpty clauses of
    Just clauses -> compileClauses parent ins clauses
    -- If there are no more clauses left to test, then the Hugr panics
    Nothing -> let sig = FunctionType (snd <$> ins) outTys in
      addNodeWithInputs "Panic" (OpCustom (CustomOp parent "brat" "panic" sig [])) ins outTys

  didMatch :: [HugrType] -> NodeId -> [TypedPort] -> Compile [TypedPort]
  didMatch outTys parent ins = gets bratGraph >>= \(ns,_) -> case ns M.! rhs of
    BratNode (src :>>: tgt) _ _ -> do
      dfgId <- addNode "DidMatch_DFG" (OpDFG (DFG parent (FunctionType (snd <$> ins) outTys)))
      compileBox (src, tgt) dfgId
      for (zip (fst <$> ins) (Port dfgId <$> [0..])) addEdge
      pure $ zip (Port dfgId <$> [0..]) outTys
    _ -> error "RHS should be a box node"

compileBox :: (Name, Name) -> NodeId -> Compile ()
-- note: we used to compile only KernelNode's here, this may not be right
compileBox (src, tgt) parent = for_ [src, tgt] (compileWithInputs parent)

compileWithInputs :: NodeId -> Name -> Compile (Maybe NodeId)
compileWithInputs parent name = gets compiled <&> M.lookup name >>= \case
  Just nid -> pure (Just nid)
  Nothing -> do
    (_, es) <- gets bratGraph
    let in_edges = [((src, ty), portNum) | (src, ty, (In edgTgt portNum)) <- es, edgTgt == name]
    compileNode in_edges >>= \case
      Nothing -> pure Nothing
      Just (tgtNodeId, edges) -> do
        registerCompiled name tgtNodeId
        for edges (\(src, tgtPort) -> addEdge (src, Port tgtNodeId tgtPort))
        pure $ Just tgtNodeId
 where
  walkGraph n = compileWithInputs parent n

  -- If we only care about the node for typechecking, then drop it and return `Nothing`.
  -- Otherwise, NodeId of compiled node, and list of Hugr in-edges (source and target-port)
  compileNode :: [((OutPort, Val Z), Int)] -> Compile (Maybe (NodeId, [(PortId NodeId, Int)]))
  compileNode in_edges | isJust (hasPrefix ["checking", "globals", "decl"] name) = do
    -- reference to a top-level decl. Every such should be in the decls map.
    -- We need to return value of each type (perhaps to be indirectCalled by successor).
    -- Note this is where we must compile something different *for each caller* by clearing out the `compiled` map for each function
    let inTys = map (snd . fst) $ sortBy (comparing snd) in_edges
    hTys <- for inTys compileType
    decls <- gets decls
    let (funcDef, extra_call) = decls M.! name
    nod <- case extra_call of
      True -> addNode ("direct_call(" ++ show funcDef ++ ")")
                  (OpCall (CallOp parent (FunctionType [] hTys)))
      -- We are loading idNode as a value (not an Eval'd thing), and it is a FuncDef directly
      -- corresponding to a Brat TLD (not that produces said TLD when eval'd)
      False -> addNode ("load_thunk(" ++ show funcDef ++ ")")
                  (OpLoadConstant (LoadConstantOp parent (let [ty] = hTys in ty)))
    -- the only input
    pure $ Just (nod, [(Port funcDef 0, 0)])
  compileNode in_edges = do
    (ns, _) <- gets bratGraph
    let node = ns M.! name
    trackM ("compileNode (" ++ show parent ++ ") " ++ show name ++ " " ++ show node)
    nod_edge_info <- case node of
      (BratNode thing ins outs) -> compileNode' thing ins outs
      (KernelNode thing ins outs) -> compileNode' thing ins outs
    case nod_edge_info of
      Nothing -> pure Nothing
      Just (node, tgtOffset, extra_edges) -> do
        trans_edges <- catMaybes <$> for in_edges (\((Ex src srcPort, _), tgtPort) ->
            walkGraph src <&> fmap (\srcNodeId -> (Port srcNodeId srcPort, tgtPort + tgtOffset))
          )
        pure $ Just (node, extra_edges ++ trans_edges)

  default_edges :: NodeId -> Maybe (NodeId, Int, [(PortId NodeId, Int)])
  default_edges nid = Just (nid, 0, [])

  compileNode' :: NodeType m -> [(PortName, Val Z)] -> [(PortName, Val Z)]
                  -- Result is nodeid, port offset, *extra* edges
               -> Compile (Maybe (NodeId, Int, [(PortId NodeId, Int)]))
  compileNode' thing ins outs = case thing of
    Const tm -> default_edges <$> compileConst parent tm (snd $ head outs)
    Splice (Ex outNode _) -> default_edges <$> do
      ins <- traverse (compileType . snd) ins
      outs <- traverse (compileType . snd) outs
      let sig = FunctionType ins outs
      case hasPrefix ["checking", "globals", "prim"] outNode of
        -- If we're evaling a Prim, we add it directly into the kernel graph
        Just suffix -> do
          (ns, _) <- gets bratGraph
          case M.lookup outNode ns of
            Just (BratNode (Prim (ext,op)) _ [(_, VFun Kerny _)]) -> do
              addNode (show suffix) (OpCustom (CustomOp parent ext op sig []))
            x -> error $ "Expected a Prim kernel node but got " ++ show x
        -- All other evaled things are turned into holes to be substituted later
        Nothing -> do
          hole <- do
            st <- get
            let h = (holes st)
            put (st { holes = h :< name})
            pure (length h)
          addNode ("hole " ++ show hole) (OpCustom (holeOp parent hole sig))
    -- A reference to a primitive op which exists in hugr.
    -- This should only have one outgoing wire which leads to an `Id` node for
    -- the brat representation of the function, and that wire should have a
    -- function type
    Prim _ -> error $ "TODO: Compiling a Prim node being used as a thunk, not directly Evaled."
                      ++ " Should construct trivial 4-node DFG+I/O+CustomOp Hugr."

    -- Check if the node has prefix "globals", hence should be a direct call
    Eval (Ex outNode outPort) -> do
      ins <- traverse (compileType . snd) ins
      outs <- traverse (compileType . snd) outs
      (ns, _) <- gets bratGraph
      decls <- gets decls
      case hasPrefix ["checking", "globals", "prim"] outNode of
        -- Callee is a Prim node, insert Hugr Op; first look up outNode in the BRAT graph to get the Prim data
        Just suffix -> default_edges <$> case M.lookup outNode ns of
          Just (BratNode (Prim (ext,op)) _ _) -> do
            addNode (show suffix) (OpCustom (CustomOp parent ext op (FunctionType ins outs) []))
          x -> error $ "Expected a Prim node but got " ++ show x
        Nothing -> case hasPrefix ["checking", "globals"] outNode of
          -- Callee is a user-defined global def that, since it does not require an "extra" call, can be turned from IndirectCall to direct.
          Just _ | (funcDef, False) <- fromJust (M.lookup outNode decls) -> do
                callerId <- addNode ("direct_call(" ++ show funcDef ++ ")")
                                    (OpCall (CallOp parent (FunctionType ins outs)))
                -- Add the static edge from the FuncDefn node to the port *after*
                -- all of the dynamic arguments to the Call node.
                -- This is because in hugr, static edges (like the graph arg to a
                -- Call) come after dynamic edges
                pure $ Just (callerId, 0, [(Port funcDef 0, length ins)])
          -- Either not global, or we must evaluate the global -- so an indirect call of a graph on a wire
          -- (If it's a global, compileWithInputs will generate extra no-args Call,
          -- since extra_call==True; we just turned the (Eval+)LoadFunction case into a direct Call above)
          _ -> compileWithInputs parent outNode >>= \case
            Just calleeId -> do
              callerId <- addNode ("indirect_call(" ++ show calleeId ++ ")")
                                  (OpCallIndirect (CallIndirectOp parent (FunctionType ins outs)))
              -- for an IndirectCall, the callee (thunk, function value) is the *first*
              -- Hugr input. So move all the others along, and add that extra edge.
              pure $ Just (callerId, 1, [(Port calleeId outPort, 0)])
            Nothing -> error "Callee has been erased"

    (src :>>: tgt) -> default_edges <$>
      -- We need to figure out if this thunk contains a brat- or a kernel-computation
      case outs of
        [(_, VFun Kerny cty)] -> nodeId . fst <$> compileKernBox parent name (compileBox (src, tgt)) cty
        [(_, VFun Braty _)] -> error "todo: variables captured by thunk - lambda-lift, partial"
        _ -> error $ "Unexpected out-ports on thunk: " ++ show outs

    Source -> default_edges <$> do
      outs <- traverse (compileType . snd) outs
      addNode "Input" (OpIn (InputNode parent outs))
    Target -> default_edges <$> do
      ins <- traverse (compileType . snd) ins
      addNode "Output" (OpOut (OutputNode parent ins))

    Id | Nothing <- hasPrefix ["checking", "globals", "decl"] name -> default_edges <$> do
      -- not a top-level decl, just compile it as an Id (TLDs handled in compileNode)
      let [(_,ty)] = ins -- fail if more than one input
      ty <- compileType ty
      addNode "Id" (OpNoop (NoopOp parent ty))
    Constructor c -> default_edges <$> do
      let b = case c of
            CFalse -> False
            CTrue -> True
            _ -> error $ "Don't know how to compile " ++ show c
      -- A boolean value is a tuple and a tag
      -- This is the same thing that happens in Brat.Checker.Clauses (makeDiscriminator)
      makeTuple <- freshNode "bool.MakeTuple"
      addOp (OpMakeTuple (MakeTupleOp parent [])) makeTuple
      tag <- freshNode "bool.tag"
      addOp (OpTag (TagOp parent (if b then 1 else 0) [HTTuple [], HTTuple []])) tag
      addEdge (Port makeTuple 0, Port tag 0)
      pure tag
    ArithNode op -> default_edges <$> compileArithNode parent op (snd $ head ins)
    Selector _c -> error "Todo: selector"
    x -> error $ show x ++ " should have been compiled outside of compileNode"

compileKernBox :: NodeId -> Name -> (NodeId -> Compile ()) -> CTy Kernel Z -> Compile TypedPort
compileKernBox parent name contents cty = do
  -- compile kernel nodes only into a Hugr with "Holes"
  -- when we see a Splice, we'll record the func-port onto a list
  -- return a Hugr with holes
  box_sig <- body <$> compileSig cty
  let box_ty = HTFunc $ PolyFuncType [] box_sig
  st <- gets store
  g <- gets bratGraph
  -- Build a template Hugr with a new run of the Monad.
  -- First, we fork off a new namespace
  (holelist, templateHugr) <- "KernelBox" -! do
    ns <- gets nameSupply
    let templateCtx = flip execState (emptyCS g ns st) $ do
          -- Make a DFG node at the root. We can't use `addNode` since the
          -- DFG needs itself as parent
          dfg_id <- freshNode ("KernelBox_" ++ show name)
          st <- get
          put (st { nodes = (OpDFG $ DFG dfg_id box_sig, dfg_id) : nodes st })
          contents dfg_id
    let holelist = holes templateCtx <>> [] -- index 0 (earliest elem) now outermost
    let templateHugr = renameAndSortHugr (nodes templateCtx) (edges templateCtx)
    pure (holelist, templateHugr)

  -- now make classical func
  templateConstNode <- addNode ("ConstTemplate_" ++ show name) (OpConst (ConstOp parent (HCFunction templateHugr) box_ty))
  templatePort <- head <$> addNodeWithInputs ("LoadTemplate_" ++ show name) (OpLoadConstant (LoadConstantOp parent box_ty))
                  [(Port templateConstNode 0, box_ty)] [box_ty]

  -- For each hole in the template, compile the kernel that should be spliced
  -- in and record its signature.
  hole_ports <- for holelist (\splice -> do
    let (KernelNode (Splice (Ex kernel_src port)) ins outs) = (fst g) M.! splice
    ins <- traverse (compileType . snd) ins
    outs <- traverse (compileType . snd) outs
    kernel_src <- compileWithInputs parent kernel_src <&> fromJust
    pure (Port kernel_src port, HTFunc (PolyFuncType [] (FunctionType ins outs))))

  -- Add a substitute node to fill the holes in the template
  let hole_sigs = [ body poly | (_, HTFunc poly) <- hole_ports ]
  head <$> addNodeWithInputs ("subst_" ++ show name) (OpCustom (substOp parent box_sig hole_sigs)) (templatePort : hole_ports) [box_ty]


-- We get a bunch of TypedPorts which are associated with Srcs in the BRAT graph.
-- Then, we'll perform a sequence of matches on those ports
-- Return a sum whose first component is the types we started with in the order
-- specified by the portTable argument.
--
-- In the happy path we return wires in the order of `matchOutputs`
-- otherwise, the order is the same as how they came in via the portTable
compileMatchSequence :: NodeId -- The parent node
                     -> [(Src  -- Things we've matched or passed through, coming from an Input node
                         ,TypedPort)] -- This portTable and `matchInputs` should be in the same order
                     -> MatchSequence HugrType
                     -> Compile TypedPort
compileMatchSequence parent portTable (MatchSequence {..}) = do
  unless
    ((second snd <$> portTable) == matchInputs)
    (error "compileMatchSequence assert failed")
  let sumTy = SoR [snd <$> matchInputs, snd <$> matchOutputs]
  case matchTests of
    (src, primTest):tests -> do
      -- Pick the port corresponding to the source we want to test
      let ((_, typedPort), (left, right)) = head $ filter ((src ==) . fst . fst) (foci portTable)
      let others = left <>> right
      -- Compile the primitive test, giving us a single `testResult` port with a
      -- sum type (either the thing we looked at or it's pieces) and a bunch of
      -- other inputs
      testResult <- compilePrimTest parent typedPort primTest
      let testIx = length left
      let remainingMatchTests = MatchSequence (primTestOuts primTest ++ (second snd <$> others)) tests matchOutputs
      ports <- makeConditional parent testResult (snd <$> others)
               [("didNotMatch", didNotMatchCase testIx sumTy)
               ,("didMatch",    didMatchCase testIx (primTest, snd typedPort) remainingMatchTests sumTy)]
      case ports of
        [port] -> pure port
        _ -> error "Expected exactly one output port from makeConditional"

    [] -> do
      -- Reorder into `matchOutputs` order
      let ins = reorderPortTbl portTable (fst <$> matchOutputs)
      -- Need to pack inputs into a tuple before feeding them into a tag node
      ports <- makeRowTag "Success" parent 1 sumTy ins
      case ports of
        [port] -> pure port
        _ -> error "Expected one port out of tag node"
 where
  reorderPortTbl :: [(Src, TypedPort)] -> [Src] -> [TypedPort]
  reorderPortTbl portTbl = fmap (fromJust . flip lookup portTbl)

  didMatchCase :: Int -- The index to put the rebuilt thing back in the wires in case of failure
               -> (PrimTest HugrType  -- The test that just matched, for book keeping
                  ,HugrType) -- and the type of the thing it was done on,
               -> MatchSequence HugrType -- The remaining tests for further matching
               -> SumOfRows
               -> NodeId
               -> [TypedPort]
               -> Compile [TypedPort]
  didMatchCase ix (prevTest, oldTy) ms@(MatchSequence{..}) sumTy parent ins = do
    -- Remember which port a src corresponds to
    let portTable = zip (fst <$> matchInputs) ins
    didAllTestsSucceed <- compileMatchSequence parent portTable ms
    makeConditional parent didAllTestsSucceed []
      [("Undo", undo)
      ,("AllMatched", allMatched)
      ]
   where
    -- All of the results from tests will be at the front of `ins`.
    undo :: NodeId
         -> [TypedPort]
         -> Compile [TypedPort]
    undo parent ins = do
      -- Test results, and the rest of the inputs
      let (refined, other) = splitAt (length (primTestOuts prevTest)) ins
      undoPort <- undoPrimTest parent refined oldTy prevTest
      -- Put it back in the right place
      let (as, bs) = splitAt ix other
      let ins = (as ++ undoPort : bs)
      makeRowTag "Fail_Undo" parent 0 sumTy ins

    allMatched :: NodeId -> [TypedPort] -> Compile [TypedPort]
    allMatched parent = makeRowTag "AllMatched" parent 1 sumTy

  didNotMatchCase :: Int -- The index at which to put the thing we inspected in outputs
                  -> SumOfRows
                  -> NodeId
                  -> [TypedPort]
                  -> Compile [TypedPort]
  didNotMatchCase _ _ _ [] = error "No scrutinee input in didNotMatchCase"
  didNotMatchCase ix sumTy parent (scrutinee:ins) = do
    let (as, bs) = splitAt ix ins
    -- We need to wire inputs to a `Tag0`, but bringing the tested src back to
    -- the original position
    let ins = as ++ scrutinee:bs
    makeRowTag "DidNotMatch" parent 0 sumTy ins

makeRowTag :: String -> NodeId -> Int -> SumOfRows -> [TypedPort] -> Compile [TypedPort]
makeRowTag hint parent tag sor@(SoR sumRows) ins = assert (sumRows !! tag == (snd <$> ins)) $ do
  tuple <- addNodeWithInputs (hint ++ "_MakeTuple") (OpMakeTuple (MakeTupleOp parent (snd <$> ins))) ins [HTTuple (snd <$> ins)]
  addNodeWithInputs (hint ++ "_Tag") (OpTag (TagOp parent tag (HTTuple <$> sumRows))) tuple [compileSumOfRows sor]

getSumVariants :: HugrType -> [[HugrType]]
getSumVariants (HTSum (SU (UnitSum n))) = replicate n []
getSumVariants (HTSum (SG (GeneralSum rows))) = fromTuple <$> rows
 where
  fromTuple :: HugrType -> [HugrType]
  fromTuple (HTTuple row) = row
  fromTuple _ = error "Expected row of tuples in getSumVariants"
getSumVariants ty = error $ "Expected a sum type, got " ++ show ty


-- This should only be called by the logic which creates conditionals, because
-- wires that exist in the brat graph are already going to be added at the end.
addNodeWithInputs :: String -> (HugrOp NodeId) -> [TypedPort]
                   -> [HugrType] -- The types of the outputs
                   -> Compile [TypedPort] -- The output wires
addNodeWithInputs name op inWires outTys = do
  nodeId <- addNode name op
  for (zip (fst <$> inWires) (Port nodeId <$> [0..])) addEdge
  pure $ zip (Port nodeId <$> [0..]) outTys

makeConditional :: NodeId    -- Parent node id
                -> TypedPort -- The discriminator
                -> [TypedPort] -- Other inputs
                -> [(String, NodeId -> [TypedPort] -> Compile [TypedPort])] -- Must be ordered
                -> Compile [TypedPort]
makeConditional parent discrim otherInputs cases = do
  condId <- freshNode "Conditional"
  let rows = getSumVariants (snd discrim)
  outTyss <- for (zip (zip [0..] cases) rows) (\((ix, (name, f)), row) -> makeCase condId name ix (row ++ (snd <$> otherInputs)) f)
  unless
    (allRowsEqual outTyss)
    (error "Conditional output types didn't match")
  st <- get
  put (st { nodes = (OpConditional
                     (Conditional parent rows
                      (snd <$> otherInputs)
                      (head outTyss))
                    ,condId)
                    : nodes st })
  addEdge (fst discrim, Port condId 0)
  traverse_ addEdge (zip (fst <$> otherInputs) (Port condId <$> [1..]))
  pure $ zip (Port condId <$> [0..]) (head outTyss)
 where
  makeCase :: NodeId -> String -> Int -> [HugrType] -> (NodeId -> [TypedPort] -> Compile [TypedPort]) -> Compile [HugrType]
  makeCase parent name ix tys f = do
    caseId <- freshNode name
    inpId <- addNode ("Input_" ++ name) (OpIn (InputNode caseId tys))
    outs <- f caseId (zipWith (\offset ty -> (Port inpId offset, ty)) [0..] tys)
    let outTys = snd <$> outs

    outId <- addNode ("Output" ++ name) (OpOut (OutputNode caseId outTys))
    for (zip (fst <$> outs) (Port outId <$> [0..])) addEdge

    st <- get
    put (st { nodes = (OpCase (ix, Case parent (FunctionType tys outTys)), caseId) : nodes st })
    pure outTys

  allRowsEqual :: [[HugrType]] -> Bool
  allRowsEqual [] = True
  allRowsEqual [_] = True
  allRowsEqual (x:xs) = all (x==) xs

compilePrimTest :: NodeId
                -> TypedPort -- The thing that we're testing
                -> PrimTest HugrType -- The test to run
                -> Compile TypedPort
compilePrimTest parent (port, ty) (PrimCtorTest c tycon unpackingNode outputs) = do
  let sumOut = (HTSum (SG (GeneralSum [HTTuple [ty], HTTuple (snd <$> outputs)])))
  let sig = FunctionType [ty] [sumOut]
  testId <- addNode ("PrimCtorTest " ++ show c)
            (OpCustom (CustomOp
                       parent
                       "BRAT"
                       ("PrimCtorTest::" ++ show tycon ++ "::" ++ show c)
                       sig
                       []))
  addEdge (port, Port testId 0)
  registerCompiled unpackingNode testId
  pure (Port testId 0, sumOut)
compilePrimTest parent port@(_, ty) (PrimLitTest tm) = do
  -- Make a Const node that holds the value we test against
  constId <- addNode "LitConst" (OpConst (ConstOp parent (constFromSimple tm) ty))
  loadPort <- head <$> addNodeWithInputs "LitLoad" (OpLoadConstant (LoadConstantOp parent ty))
                       [(Port constId 0, ty)] [ty]
  -- Connect to a test node
  let sumOut = HTSum (SG (GeneralSum [HTTuple [ty], HTTuple []]))
  let sig = FunctionType [ty, ty] [sumOut]
  head <$> addNodeWithInputs ("PrimLitTest " ++ show tm)
           (OpCustom (CustomOp parent "BRAT" ("PrimLitTest::" ++ show ty) sig []))
           [port, loadPort]
           [sumOut]

undoPrimTest :: NodeId
             -> [TypedPort] -- The inputs we have to put back together
             -> HugrType -- The type of the thing we're making
             -> PrimTest HugrType -- The test to undo
             -> Compile TypedPort
undoPrimTest parent inPorts outTy (PrimCtorTest c tycon _ _) = do
  let sig = FunctionType (snd <$> inPorts) [outTy]
  head <$> addNodeWithInputs
           ("UndoCtorTest " ++ show c)
           (OpCustom (CustomOp parent "BRAT" ("Ctor::" ++ show tycon ++ "::" ++ show c) sig []))
           inPorts
           [outTy]
undoPrimTest parent inPorts outTy (PrimLitTest tm) = do
  unless (null inPorts) $ error "Unexpected inPorts"
  constId <- addNode "LitConst" (OpConst (ConstOp parent (constFromSimple tm) outTy))
  head <$> addNodeWithInputs "LitLoad" (OpLoadConstant (LoadConstantOp parent outTy))
           [(Port constId 0, outTy)] [outTy]

compileBinderTy :: Modey m -> BinderType m -> Compile HugrType
compileBinderTy m = compileType . binderToValue m


-- Create a module and FuncDecl nodes inside it for all of the functions given as argument
compileModule :: VEnv
              -> Compile ()
compileModule venv = do
  moduleNode <- mkModuleNode
  -- Prepare FuncDef nodes for all functions. Every "noun" also requires a Function
  -- to compute its value.
  bodies <- for decls (\(fnName, idNode) -> do
    (funTy, extra_call, body) <- analyseDecl idNode
    defNode <- addNode (show fnName ++ "_def") (OpDefn $ FuncDefn moduleNode (show fnName) funTy)
    registerFuncDef idNode (defNode, extra_call)
    pure (body defNode)
    )
  for_ bodies (\body -> do
    st <- get
    -- At the start of each function, clear out the `compiled` map - these are
    -- the nodes compiled (usable) within that function. Generally Brat-graph nodes
    -- are only reachable from one TLD, but the `Id` nodes are shared, and must have
    -- their own LoadConstant/extra-Call/etc. *within each function*.
    put st { compiled = M.empty }
    body)
 where
  -- Given the Brat-Graph Id node for the decl, work out how to compile it (later);
  -- return the type of the Hugr FuncDefn, whether said FuncDefn requires an extra Call,
  -- and the procedure for compiling the contents of the FuncDefn for execution later,
  -- *after* all such FuncDefns have been registered
  analyseDecl :: Name -> Compile (PolyFuncType, Bool, (NodeId -> Compile ()))
  analyseDecl idNode = do
    (ns, es) <- gets bratGraph
    let srcPortTys = [(srcPort, ty) | (srcPort, ty, In tgt _) <- es, tgt == idNode ]
    maybeDirect <- case srcPortTys of
      [(Ex input 0, _)] | Just srcNode <- M.lookup input ns -> canCompileDirect input srcNode
      _ -> pure Nothing
    case maybeDirect of
       Just func -> pure func
       Nothing -> do -- a computation, or several values
        outs <- for (map snd srcPortTys) compileType -- note compiling already-erased types, is this right?
        pure (funcReturning outs, True, compileNoun outs (map fst srcPortTys))

  canCompileDirect :: Name -> Node -> Compile (Maybe (PolyFuncType, Bool, (NodeId -> Compile ())))
  canCompileDirect _ (BratNode (src :>>: tgt) _ [(_, VFun Braty cty)]) = do
    sig <- compileSig cty
    pure $ Just (sig, False, compileBox (src, tgt))
  canCompileDirect _ (BratNode (FunClauses cs) _ [(_, VFun _ cty)]) = do
    sig <- compileSig cty
    let (FunctionType ins _) = body sig
    pure $ Just (sig, False, compileFunClauses ins cs)
  -- Really these two are not compiled direct, and should be dealt with via compileNoun,
  -- but until compileNode correctly handles each of these, we have to do so here:
  canCompileDirect input (KernelNode (FunClauses cs) _ [(_, VFun Kerny cty)]) = do
    kernTy <- compileSig cty
    let (FunctionType kIns _) = body kernTy
    let thunkTy = HTFunc kernTy
    pure $ Just (funcReturning [thunkTy], True, \parent ->
          withIO parent thunkTy $ compileKernBox parent input (compileFunClauses kIns cs) cty)
  canCompileDirect input (BratNode (src :>>: tgt) [] [(_, VFun Kerny cty)]) = do
        -- We're compiling, e.g.
        --   f :: { Qubit -o Qubit }
        --   f = { h; circ(pi) }
        -- Although this looks like a constant kernel, we'll have to compile the
        -- computation that produces this constant. We do so by making a FuncDefn
        -- that takes no arguments and produces the constant kernel graph value.
        thunkTy <- HTFunc <$> compileSig cty
        pure $ Just (funcReturning [thunkTy], True, \parent ->
          withIO parent thunkTy $ compileKernBox parent input (compileBox (src, tgt)) cty)
  canCompileDirect _ _ = pure Nothing

  withIO :: NodeId -> HugrType -> Compile TypedPort -> Compile ()
  withIO parent output c = do
    addNode "input" (OpIn (InputNode parent []))
    output <- addNode "output" (OpOut (OutputNode parent [output]))
    wire <- c
    addEdge (fst wire, Port output 0)

  -- top-level decls that are not Prims. RHS is the brat idNode
  decls :: [(UserName, Name)]
  decls = do -- in list monad, no Compile here
            (fnName, wires) <- (M.toList venv)
            let (Ex idNode _) = end (fst $ head wires) -- would be better to check same for all rather than just head
            case hasPrefix ["checking","globals","decl"] idNode of
              Just _ -> pure (fnName, idNode) -- assume all ports are 0,1,2...
              Nothing -> []

  mkModuleNode :: Compile NodeId
  mkModuleNode = do
    id <- freshNode "module"
    st <- get
    put (st { nodes = (OpMod $ ModuleOp id, id) : nodes st })
    pure id

  funcReturning :: [HugrType] -> PolyFuncType
  funcReturning outs = PolyFuncType [] (FunctionType [] outs)

compileNoun :: [HugrType] -> [OutPort] -> NodeId -> Compile ()
compileNoun outs srcPorts parent = do
  addNode "input" (OpIn (InputNode parent []))
  output <- addNode "output" (OpOut (OutputNode parent outs))
  for_ (zip [0..] srcPorts) (\(outport, Ex src srcPort) ->
    compileWithInputs parent src >>= \case
      Just nodeId -> addEdge (Port nodeId srcPort, Port output outport) $> ()
      Nothing -> pure () -- if input not compilable, leave edge missing in Hugr - or just error?
    )

compile :: Store
        -> Namespace
        -> Graph
        -> VEnv
        -> BS.ByteString
compile store ns g venv
  = evalState
    (trackM "compileFunctions" *>
     compileModule venv *>
     trackM "dumpJSON" *>
     dumpJSON
    )
    (emptyCS g ns store)
