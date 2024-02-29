{-# LANGUAGE AllowAmbiguousTypes, FlexibleContexts, ScopedTypeVariables,
TypeApplications #-}

module Brat.Checker.Helpers {-(pullPortsRow, pullPortsSig
                            ,simpleCheck
                            ,combineDisjointEnvs
                            ,ensureEmpty, noUnders
                            ,rowToSig
                            ,showMode, getVec
                            ,mkThunkTy
                            ,wire
                            ,next, knext, anext
                            ,kindType, getThunks
                            ,binderToValue, valueToBinder
                            ,kConFields
                            ,defineSrc, defineTgt
                            ,declareSrc, declareTgt
                            ,makeBox
                            ,uncons
                            ,evalBinder
                            ,evalSrcRow, evalTgtRow
                            )-} where

import Brat.Checker.Monad (Checking, CheckingSig(..), err, typeErr, captureOuterVars, kindArgRows)
import Brat.Checker.Types
import Brat.Error (ErrorMsg(..))
import Brat.Eval (Eval(eval), EvMode(..), kindType)
import Brat.FC (FC)
import Brat.Graph (Node(..), Thing(..))
import Brat.Naming (Name)
import Brat.Syntax.Common
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Hasochism
import Util (zip_same_length)

import Control.Monad (forM, unless)
import Control.Monad.Freer (req, Free(Ret))
import Control.Arrow ((***))
import Control.Exception (assert)
import Data.Bifunctor
import Data.List (intercalate)
import Data.Maybe (fromJust)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding (last)

simpleCheck :: Modey m -> Val Z -> SimpleTerm -> Either ErrorMsg ()
simpleCheck Braty TNat (Num n) | n >= 0 = pure ()
simpleCheck Braty TInt (Num _) = pure ()
simpleCheck Braty TFloat (Float _) = pure ()
simpleCheck Braty TText (Text _) = pure ()
simpleCheck _ ty tm = Left $ TypeErr $ unwords
                      ["Expected something of type"
                      ,"`" ++ show ty ++ "`"
                      ,"but got"
                      ,"`" ++ show tm ++ "`"
                      ]

-- Port pulling, but with no moving of/around binders (TODO)
pull1PortRo :: MODEY m
            => Modey m
            -> PortName -- The port we want to pull to the front
            -> Bwd (PortName, Val bot) -- The things we've passed so far
            -> Ro m bot top -- The row we've got left to traverse
            -> Checking ((PortName, Val bot), Ro m bot top)
-- TODO: Make an `Error` constructor for this
pull1PortRo _ p _ R0 = fail $ "Port not found: " ++ p
pull1PortRo m p stuff (RPr (p', ty) ro)
 | p == p' = if portNameExists m p ro
   then err (AmbiguousPortPull p (show (RPr (p', ty) ro)))
   else pure ((p', ty), rebuildRo m ro (stuff <>> []))
 | otherwise = pull1PortRo m p (stuff :< (p', ty)) ro
 where
  rebuildRo :: Modey m
            -> Ro m bot top -- The row that we still haven't traversed
            -> [(PortName, Val bot)] -- The stuff we've passed
            -> Ro m bot top
  rebuildRo _ ro [] = ro
  rebuildRo m ro (x:xs) = RPr x (rebuildRo m ro xs)

  portNameExists :: Modey m -> PortName -> Ro m bot top -> Bool
  portNameExists _ _ R0 = False
  portNameExists m p (RPr (p', _) ro)
   | p == p' = True
   | otherwise = portNameExists m p ro
  portNameExists Braty p (REx (p', _) (_ ::- ro))
   | p == p' = True
   | otherwise = portNameExists Braty p ro
-- TODO: Make an `Error` for this
-- TODO: Enable this later
pull1PortRo Braty _ _ (REx _ _) = fail "Port pull past a type binder"

pullPortsRo :: MODEY m => Modey m -> [PortName] -> Ro m bot top -> Checking (Ro m bot top)
pullPortsRo _ [] ro = pure ro
pullPortsRo m (p:ps) ro = do
  (x, ro) <- pull1PortRo m p B0 ro
  RPr x <$> pullPortsRo m ps ro

pullPortsRow :: Show ty
             => [PortName]
             -> [(NamedPort e, ty)]
             -> Checking [(NamedPort e, ty)]
pullPortsRow = pullPorts portName showRow

pullPortsSig :: Show ty
             => [PortName]
             -> [(PortName, ty)]
             -> Checking [(PortName, ty)]
pullPortsSig = pullPorts id showSig

pullPorts :: forall a ty. Show ty
          => (a -> PortName) -- A way to get a port name for each element
          -> ([(a, ty)] -> String) -- A way to print the list
          -> [PortName] -- Things to pull to the front
          -> [(a, ty)]  -- The list to rearrange
          -> Checking [(a, ty)]
pullPorts _ _ [] types = pure types
pullPorts toPort showFn (p:ports) types = do
  (x, types) <- pull1Port p types
  (x:) <$> pullPorts toPort showFn ports types
 where
  pull1Port :: PortName
            -> [(a, ty)]
            -> Checking ((a, ty), [(a, ty)])
  pull1Port p [] = fail $ "Port not found: " ++ p
  pull1Port p (x@(a,_):xs)
   | p == toPort a
   = if (p `elem` (toPort . fst <$> xs))
     then err (AmbiguousPortPull p (showFn (x:xs)))
     else pure (x, xs)
   | otherwise = (id *** (x:)) <$> pull1Port p xs

combineDisjointEnvs :: M.Map UserName v -> M.Map UserName v -> Checking (M.Map UserName v)
combineDisjointEnvs l r =
  let commonKeys = S.intersection (M.keysSet l) (M.keysSet r)
  in if S.null commonKeys
    then Ret $ M.union l r
    else typeErr ("Variable(s) defined twice: " ++
      (intercalate "," $ map show $ S.toList commonKeys))

ensureEmpty :: Show ty => String -> [(NamedPort e, ty)] -> Checking ()
ensureEmpty _ [] = pure ()
ensureEmpty str xs = err $ InternalError $ "Expected empty " ++ str ++ ", got:\n  " ++ showSig (rowToSig xs)

noUnders m = do
  ((outs, ()), (overs, unders)) <- m
  ensureEmpty "unders" unders
  pure (outs, overs)

rowToSig :: Traversable t => t (NamedPort e, ty) -> t (PortName, ty)
rowToSig = fmap $ \(p,ty) -> (portName p, ty)

showMode :: Modey m -> String
showMode Braty = ""
showMode Kerny = "(kernel) "

type family ThunkFCType (m :: Mode) where
  ThunkFCType Brat = FC
  ThunkFCType Kernel = ()

type family ThunkRowType (m :: Mode) where
  ThunkRowType Brat = KindOr (Term Chk Noun)
  ThunkRowType Kernel = Term Chk Noun

mkThunkTy :: Modey m
          -> ThunkFCType m
          -> [(PortName, ThunkRowType m)]
          -> [(PortName, ThunkRowType m)]
          -> Term Chk Noun
-- mkThunkTy Braty fc ss ts = C (WC fc (ss :-> ts))
mkThunkTy Braty _ ss ts = C (ss :-> ts)
mkThunkTy Kerny () ss ts = K (ss :-> ts)

anext :: forall m i j k
       . EvMode m
      => String
      -> Thing
      -> (Valz i, Some Endz)
      -> Ro m i j -- Inputs and Outputs use de Bruijn indices
      -> Ro m j k
      -> Checking (Name, Unders m Chk, Overs m UVerb, (Valz k, Some Endz))
anext str th vals0 ins outs = do
  node <- req (Fresh str) -- Pick a name for the thunk
  -- Use the new name to generate Ends with which to instantiate types
  (unders, vals1) <- endPorts node InEnd In 0 vals0 ins
  (overs, vals2)  <- endPorts node ExEnd Ex 0 vals1 outs
  () <- case modey @m of
    Braty -> sequence_ $
              [ declareTgt tgt k | (tgt, Left k) <- unders ]
              ++ [ declareSrc src k | (src, Left k) <- overs ]
    Kerny -> pure ()
  let inputs  = [ (portName p, biType @m ty) | (p, ty) <- unders ]
  let outputs = [ (portName p, biType @m ty) | (p, ty) <- overs  ]

  () <- req (AddNode node (mkNode (modey @m) th inputs outputs))
  pure (node, unders, overs, vals2)
 where
  mkNode :: forall m. Modey m -> Thing
         -> [(PortName, Val Z)]
         -> [(PortName, Val Z)]
         -> Node
  mkNode Braty = BratNode
  mkNode Kerny = KernelNode

type Endz = Ny :* Stack Z End

-- endPorts instantiates the de Bruijn variables in a row with Ends
endPorts :: forall m i j port
          . EvMode m
         => Name -> (port -> End) -> (Name -> Int -> port)
         -> Int -- Next free port on the node
         -> (Valz i, Some Endz)
         -> Ro m i j
         -> Checking ([(NamedPort port, BinderType m)], (Valz j, Some Endz))
endPorts _ _ _ _ stuff R0 = pure ([], stuff)
endPorts node port2End mkPort n (ga, ez) (RPr (p,ty) ro) = do
  ty <- mEval @m ga ty
  (row, stuff) <- endPorts node port2End mkPort (n + 1) (ga, ez) ro
  pure ((NamedPort (mkPort node n) p, tyBinder @m ty):row, stuff)
endPorts node port2End mkPort n (ga, Some (ny :* endz)) (REx (p, k) (de ::- ro)) = do
  let port = mkPort node n
  let end = port2End port
  (row, stuff) <- endPorts node port2End mkPort (n + 1)
                  (ga <<+ de :<< endVal k end, Some (Sy ny :* (endz :<< end))) ro
  pure ((NamedPort port p, Left k):row, stuff)
{-
endPorts :: (?my :: Modey m, DeBruijn (BinderType m))
          => Name -> (port -> End) -> (Name -> Int -> port)
          -> Int -> (Bwd Value, Bwd End)
          -> [(PortName, BinderType m)]
          -> Checking ([(NamedPort port, BinderType m)], (Bwd Value, Bwd End))
endPorts _ _ _ _ vals [] = pure ([], vals)
endPorts node f dir i (vals, ends) ((p, ty):xs) = do
  (ty', vals') <- case doesItBind ?my ty of
    Just k -> let end = f (dir node i)
              in pure (ty, (vals :< (endVal k end), ends :< end))
    Nothing -> (,(vals, ends)) <$> case ?my of
      Braty -> eval (req . ELup) vals ty
      Kerny -> eval (req . ELup) vals ty
  (xs', vals'') <- endPorts node f dir (i + 1) vals' xs
  pure (((NamedPort (dir node i) p), ty') : xs', vals'')
-}
next :: String -> Thing -> (Valz i, Some Endz)
     -> Ro Brat i j
     -> Ro Brat j k
     -> Checking (Name, Unders Brat Chk, Overs Brat UVerb, (Valz k, Some Endz))
next = let ?my = Braty in anext

knext :: String -> Thing -> (Valz i, Some Endz)
      -> Ro Kernel i i
      -> Ro Kernel i i
      -> Checking (Name, Unders Kernel Chk, Overs Kernel UVerb, (Valz i, Some Endz))
knext = let ?my = Kerny in anext

wire :: (Src, Val Z, Tgt) -> Checking ()
wire (src, ty, tgt) = do
  ty <- eval S0 ty
  req $ Wire (end src, ty, end tgt)

-- Called by check when synthesising a function.
-- Given a row of overs which starts with some function types for the same mode:
--   * Create an eval node for each function
--   * Compute the combined overs/unders for the juxtaposition of those evals
--     (because we want to support application of juxtaposed functions)
--   * Return the eval nodes and the combined overs/unders
--
-- The functions in the overs should be Inx-closed
--
-- Unders and Overs here are respectively the inputs and outputs for the thunks
-- This is the dual notion to the overs and unders used for typechecking against
-- Hence, we return them here in the opposite order to `check`'s connectors
getThunks :: Modey m
          -> [(Src, BinderType Brat)] -- A row of 0 or more function types in the same mode
          -> Checking ([Name]
                      ,Unders m Chk
                      ,Overs m UVerb
                      )
getThunks _ [] = pure ([], [], [])
getThunks Braty row@((src, Right ty):rest) = eval S0 ty >>= \case
  (VFun Braty (ss :->> ts)) -> do
    (node, unders, overs, _) <- let ?my = Braty in
                                  anext "" (Eval (end src)) (S0, Some (Zy :* S0)) ss ts
    (nodes, unders', overs') <- getThunks Braty rest
    pure (node:nodes, unders <> unders', overs <> overs')
  (VFun _ _) -> err $ ExpectedThunk (showMode Braty) (showRow row)
  v -> typeErr $ "Force called on non-thunk: " ++ show v
getThunks Kerny row@((src, Right ty):rest) = eval S0 ty >>= \case
  (VFun Kerny (ss :->> ts)) -> do
    (node, unders, overs, _) <- let ?my = Kerny in
                                  anext "" (Eval (end src)) (S0, Some (Zy :* S0)) ss ts
    (nodes, unders', overs') <- getThunks Kerny rest
    pure (node:nodes, unders <> unders', overs <> overs')
  (VFun _ _) -> err $ ExpectedThunk (showMode Kerny) (showRow row)
  v -> typeErr $ "Force called on non-(kernel)-thunk: " ++ show v
getThunks Braty ((src, Left (Star args)):rest) = do
  (node, unders, overs) <- case bwdStack (B0 <>< args) of
    Some (_ :* stk) -> do
      let (ri,ro) = kindArgRows stk
      (node, unders, overs, _) <- next "" (Eval (end src)) (S0, Some (Zy :* S0)) ri ro
      pure (node, unders, overs)
  (nodes, unders', overs') <- getThunks Braty rest
  pure (node:nodes, unders <> unders', overs <> overs')
getThunks m ro = err $ ExpectedThunk (showMode m) (showRow ro)

binderToValue :: Modey m -> BinderType m -> Val Z
binderToValue Braty (Left k) = kindType k
binderToValue Braty (Right ty) = ty
binderToValue Kerny v = v

valueToBinder :: Modey m -> Val Z -> BinderType m
valueToBinder Braty = Right
valueToBinder Kerny = id

defineSrc :: Src -> Val Z -> Checking ()
defineSrc src v = req (Define (ExEnd (end src)) v)

defineTgt :: Tgt -> Val Z -> Checking ()
defineTgt tgt v = req (Define (InEnd (end tgt)) v)

declareSrc :: Src -> TypeKind -> Checking ()
declareSrc src v = req (Declare (ExEnd (end src)) v)

declareTgt :: Tgt -> TypeKind -> Checking ()
declareTgt tgt v = req (Declare (InEnd (end tgt)) v)

-- listToRow :: [(PortName, BinderType m)] -> Ro m Z i
-- listToRow [] = R0
-- listToRow ((

-- Build a box corresponding to the inside of a thunk
makeBox :: (?my :: Modey m, EvMode m)
        => String -- A label for the nodes we create
        -> CTy m Z
        -> ((Overs m UVerb, Unders m Chk) -> Checking a) -- checks + builds the body using srcs/tgts from the box
        -> Checking ((Src, BinderType Brat), a)
makeBox name cty@(ss :->> ts) body = do
  (src, _, overs, ctx) <- anext (name ++ "/in") Source (S0, Some (Zy :* S0)) R0 ss
  (tgt, unders, _, _) <- anext (name ++ "/out") Target ctx ts R0
  case (?my, body) of
    (Kerny, _) -> do
      bres <- body (overs, unders)
      (_,_,[thunk],_) <- next (name ++ "_thunk") (src :>>: tgt) (S0, Some (Zy :* S0))
                              R0 (RPr ("thunk", VFun Kerny cty) R0)
      pure (thunk, bres)
    (Braty, body) -> do
      let n_args = length overs
      (bres, captures) <- captureOuterVars src (length overs) $ body (overs, unders)
      inner_outer_srcs :: [[((Src, BinderType Brat), Src)]] <- forM (M.assocs captures) $ \(var, outports) ->
        fromJust . zip_same_length outports . map fst . fromJust <$> req (VLup var)
      let new_inports = M.fromList $ map
            (\((NamedPort {end = Ex isrc n, portName=pn}, ty), _) -> assert (src == isrc) (n, (pn, ty)))
            (concat inner_outer_srcs)
      unless ((M.keys new_inports) == [n_args..n_args + length new_inports - 1]) $ err $ InternalError "wrong port numbers"
      new_inports <- pure $ M.elems new_inports -- sorted
      -- This *replaces* the earlier 'src' node with the same name, just
      -- updating the ports to include some for captured variables
      req $ AddNode src (BratNode Source [] (map (second $ biType @Brat) ((first portName <$> overs) ++ new_inports)))
      new_inports <- pure $ foldr RPr R0 (second (biType @Brat) <$> new_inports)
      -- Now make the box. This has inputs *only* for the captured variables
      -- (not the arguments - those are supplied in addition to the box when it's eval'd)
      (box_node,_,[thunk],_) <- next (name ++ "_thunk") (src :>>: tgt) (S0, Some (Zy :* S0)) new_inports (RPr ("thunk", VFun ?my cty) R0)
      -- Finally, wire captured values into box
      forM (concat inner_outer_srcs) (
        \((NamedPort {end=Ex _ n, portName=p}, ty), osrc) -> case ty of
          Right ty -> wire (osrc, ty, NamedPort {end=In box_node (n-n_args), portName=p})
          Left _ -> pure ()
        )
      pure (thunk, bres)

-- Evaluate either mode's BinderType
evalBinder :: Modey m -> BinderType m -> Checking (BinderType m)
evalBinder Kerny sty = eval S0 sty
evalBinder Braty (Right ty) = Right <$> eval S0 ty
evalBinder Braty (Left k) = pure (Left k)

-- If this goes wrong, we probably messed up writing the constructor table
natEqOrBust :: Ny i -> Ny j -> Either ErrorMsg (i :~: j)
natEqOrBust n m | Just q <- testEquality n m = pure q
natEqOrBust _ _ = Left $ InternalError "We can't count"
