{-# LANGUAGE AllowAmbiguousTypes, FlexibleContexts, ScopedTypeVariables #-}

module Brat.Checker.Helpers (pullPortsRow, pullPortsSig
                            ,simpleCheck
                            ,combineDisjointEnvs
                            ,ensureEmpty, noUnders
                            ,rowToSig
                            ,showMode, getVec
                            ,mkThunkTy
                            ,awire, wire, kwire
                            ,stypeEq, typeEq, kindEq
                            ,next, knext, anext
                            ,kindType, getThunks
                            ,binderToValue, valueToBinder
                            ,conFields
                            ,defineSrc, defineTgt
                            ,declareSrc, declareTgt
                            ,makeBox
                            ,uncons
                            ,evalBinder
                            ,evalSrcRow, evalTgtRow
                            ) where

import Brat.Checker.Monad (Checking, CheckingSig(..), err, typeErr, evSTy, evTy
                          ,stypeEq, typeEq, kindEq, captureOuterVars)
import Brat.Checker.Types
import Brat.Error (ErrorMsg(..))
import Brat.Eval ( Eval(eval) )
import Brat.FC (FC)
import Brat.Graph (Node(..), Thing(..))
import Brat.Naming (Name)
import Brat.Syntax.Common
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Util (zip_same_length)

import Control.Monad (forM, unless)
import Control.Monad.Freer (req, Free(Ret))
import Control.Arrow ((***))
import Control.Exception (assert)
import Data.Bifunctor
import Data.Functor (($>))
import Data.List (intercalate)
import Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding (last)

simpleCheck :: Show (ValueType m) => Modey m -> ValueType m -> SimpleTerm -> Checking ()
simpleCheck Braty TNat (Num n) | n >= 0 = pure ()
simpleCheck Braty TInt (Num _) = pure ()
simpleCheck Braty TBool (Bool _) = pure ()
simpleCheck Braty TFloat (Float _) = pure ()
simpleCheck Braty TText (Text _) = pure ()
simpleCheck Kerny Bit (Bool _) = pure ()
simpleCheck _ ty tm = fail (unwords [show tm, "is not of type", show ty])

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
          => (a -> PortName)
          -> ([(a, ty)] -> String)
          -> [PortName]
          -> [(a, ty)]
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

getVec :: Modey m -> ValueType m -> Maybe (ValueType m, NumValue)
getVec Braty (TVec ty (VNum n)) = Just (ty, n)
getVec Kerny (Of ty (VNum n)) = Just (ty, n)
getVec _ _ = Nothing

type family ThunkFCType (m :: Mode) where
  ThunkFCType Brat = FC
  ThunkFCType Kernel = ()

type family ThunkRowType (m :: Mode) where
  ThunkRowType Brat = KindOr (Term Chk Noun)
  ThunkRowType Kernel = SType' (Term Chk Noun)

mkThunkTy :: Modey m
          -> ThunkFCType m
          -> [(PortName, ThunkRowType m)]
          -> [(PortName, ThunkRowType m)]
          -> Term Chk Noun
-- mkThunkTy Braty fc ss ts = C (WC fc (ss :-> ts))
mkThunkTy Braty _ ss ts = C (ss :-> ts)
mkThunkTy Kerny () ss ts = K (R ss) (R ts)

kindType :: TypeKind -> Value
kindType Nat = TNat
kindType (Star []) = VCon (plain "nil") []
kindType (Star ks)
  = VFun Braty B0 $
    ((id *** (Right . kindType)) <$> ks) :-> []

anext :: forall m. (?my :: Modey m, DeBruijn (BinderType m))
      => String -> Thing
      -> (Bwd Value, Bwd End)
      -> [(PortName, BinderType m)] -- Inputs and Outputs use deBruijn indices
      -> [(PortName, BinderType m)]
      -> Checking (Name, Unders m Chk, Overs m UVerb, (Bwd Value, Bwd End))
anext str th vals0 ins outs = do
  node <- req (Fresh str) -- Pick a name for the thunk
  -- Use the new name to generate Ends with which to instantiate types
  (unders, vals1) <- endPorts node InEnd In 0 vals0 ins
  (overs, vals2)  <- endPorts node ExEnd Ex 0 vals1 outs
  () <- case ?my of
    Braty -> sequence_ $
              [ declareTgt tgt k | (tgt, Left k) <- unders ]
              ++ [ declareSrc src k | (src, Left k) <- overs ]
    Kerny -> pure ()
  () <- req (AddNode node (mkNode ?my th inputs outputs))
  pure (node, unders, overs, vals2)
 where
  mkNode :: forall m. Modey m -> Thing
         -> [(PortName, ValueType m)]
         -> [(PortName, ValueType m)]
         -> Node
  mkNode Braty = BratNode
  mkNode Kerny = KernelNode

  inputs, outputs :: [(PortName, ValueType m)]
  inputs  = [ (p, akindType ?my ty) | (p, ty) <- ins  ]
  outputs = [ (p, akindType ?my ty) | (p, ty) <- outs ]

akindType :: forall m. Modey m -> BinderType m -> ValueType m
akindType Braty = either kindType id
akindType Kerny = id

-- endPorts instantiates the deBruijn variables in a row with Ends
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

next :: String -> Thing -> (Bwd Value, Bwd End)
     -> [(PortName, BinderType Brat)]
     -> [(PortName, BinderType Brat)]
     -> Checking (Name, Unders Brat Chk, Overs Brat UVerb, (Bwd Value, Bwd End))
next = let ?my = Braty in anext

knext :: String -> Thing -> (Bwd Value, Bwd End)
      -> [(PortName, BinderType Kernel)]
      -> [(PortName, BinderType Kernel)]
      -> Checking (Name, Unders Kernel Chk, Overs Kernel UVerb, (Bwd Value, Bwd End))
knext = let ?my = Kerny in anext

awire :: (?my :: Modey m) => (Src, ValueType m, Tgt) -> Checking ()
awire (src, ty, tgt) = do
  ty <- mkT ?my ty
  req $ Wire (end src, ty, end tgt)
 where
  mkT :: Modey m -> ValueType m -> Checking (Either SValue Value)
  mkT Braty ty = Right <$> evTy ty
  mkT Kerny ty = pure $ Left ty

wire = let ?my = Braty in awire
kwire = let ?my = Kerny in awire

-- Unders and Overs here are respectively the inputs and outputs for the thunks
-- This is the dual notion to the overs and unders used for typechecking against
-- Hence, we return them here in the opposite order to `check`'s connectors
getThunks :: Modey m
          -> [(Src, BinderType Brat)]
          -> Checking ([Name]
                      ,Unders m Chk
                      ,Overs m UVerb
                      )
getThunks _ [] = pure ([], [], [])
getThunks Braty row@((src, Right ty):rest) = evTy ty >>= \case
  (VFun Braty ctx (ss :-> ts)) -> do
    (node, unders, overs, _) <- let ?my = Braty in
                                  anext "" (Eval (end src)) (ctx, B0) ss ts
    (nodes, unders', overs') <- getThunks Braty rest
    pure (node:nodes, unders <> unders', overs <> overs')
  (VFun _ _ _) -> err $ ExpectedThunk (showMode Braty) (showRow row)
  v -> typeErr $ "Force called on non-thunk: " ++ show v
getThunks Kerny row@((src, Right ty):rest) = evTy ty >>= \case
  (VFun Kerny ctx (ss :-> ts)) -> do
    (node, unders, overs, _) <- let ?my = Kerny in
                                  anext "" (Eval (end src)) (ctx, B0) ss ts
    (nodes, unders', overs') <- getThunks Kerny rest
    pure (node:nodes, unders <> unders', overs <> overs')
  (VFun _ _ _) -> err $ ExpectedThunk (showMode Kerny) (showRow row)
  v -> typeErr $ "Force called on non-(kernel)-thunk: " ++ show v
getThunks Braty ((src, Left (Star args)):rest) = do
  (node, unders, overs, _) <- next "" (Eval (end src)) (B0,B0) (second Left <$> args) [("type", Left (Star []))]
  (nodes, unders', overs') <- getThunks Braty rest
  pure (node:nodes, unders <>unders', overs <> overs')

conFields :: Show (ValueType m)
          => Modey m -> String -> ValueType m
          -> Either ErrorMsg [(PortName, ValueType m)]
-- Note: These are the only Kerny constructors
conFields Kerny "nil" (Of _ n) = valMatch n (VPNum NP0) $> []
conFields Kerny "cons" (Of elTy n) = do
  valMatch n (VPNum (NP1Plus NPVar)) >>= \case
    B0 :< pred -> pure [("head", elTy), ("tail", Of elTy pred)]
    _ -> Left $ InternalError "conFields: Multiple numvals in cons length"

conFields Braty "nil" (TList _) = pure []
conFields Braty "cons" (TList ty)
  = pure [("head", ty), ("tail", TList ty)]

conFields Braty "nil" (TVec _ n) = valMatch n (VPNum NP0) $> []
conFields Braty "cons" (TVec elTy n) = do
  valMatch n (VPNum (NP1Plus NPVar)) >>= \case
    B0 :< pred -> pure [("head", elTy), ("tail", TVec elTy pred)]
    _ -> Left $ InternalError "conFields: Multiple numvals in cons length"

conFields Braty "none" (TOption _) = pure []
conFields Braty "some" (TOption ty) = pure [("value", ty)]
conFields Braty "doub" ty = pure [("value", ty)]
conFields Braty "succ" ty = pure [("value", ty)]
conFields _ c ty = Left $ UnrecognisedConstructor c (show ty)

binderToValue :: Modey m -> BinderType m -> ValueType m
binderToValue Braty (Left k) = kindType k
binderToValue Braty (Right ty) = ty
binderToValue Kerny v = v

valueToBinder :: Modey m -> ValueType m -> BinderType m
valueToBinder Braty = Right
valueToBinder Kerny = id

defineSrc :: Src -> Value -> Checking ()
defineSrc src v = req (Define (ExEnd (end src)) v)

defineTgt :: Tgt -> Value -> Checking ()
defineTgt tgt v = req (Define (InEnd (end tgt)) v)

declareSrc :: Src -> TypeKind -> Checking ()
declareSrc src v = req (Declare (ExEnd (end src)) v)

declareTgt :: Tgt -> TypeKind -> Checking ()
declareTgt tgt v = req (Declare (InEnd (end tgt)) v)

makeBox :: (?my :: Modey m, DeBruijn (BinderType m))
        => String -- A label for the nodes we create
        -> Bwd Value -- Stuff that the function type can depend on
        -> [(PortName, BinderType m)] -- Inputs
        -> [(PortName, BinderType m)] -- Outputs
        -> ((Overs m UVerb, Unders m Chk) -> Checking a) -- checks + builds the body
        -> Checking ((Src, BinderType Brat), a)
makeBox name vctx ss ts body = do
  (src, _, overs, ctx) <- anext (name ++ "/in") Source (vctx, B0) [] ss
  (tgt, unders, _, _) <- anext (name ++ "/out") Target ctx ts []
  case (?my, ss, ts, body) of
    (Kerny, _, _, _) -> do
      bres <- body (overs, unders)
      (_,_,[thunk],_) <- next (name ++ "_thunk") (src :>>: tgt) (vctx,B0) [] [("thunk", Right (VFun ?my B0 (ss :-> ts)))]
      pure (thunk, bres)
    (Braty, ss, ts, body) -> do
      let n_args = length ss
      (bres, captures) <- captureOuterVars src (length overs) $ body (overs, unders)
      inner_outer_srcs :: [[((Src, BinderType Brat), Src)]] <- forM (M.assocs captures) $ \(var, outports) ->
        fromJust . zip_same_length outports . map fst . fromJust <$> req (VLup var)
      let new_inports = M.fromList $ map (\((NamedPort {end = Ex isrc n, portName=pn}, ty), _) -> assert (src == isrc) (n, (pn, ty))) (concat inner_outer_srcs)
      unless ((M.keys new_inports) == [n_args..n_args + length new_inports - 1]) $ err $ InternalError "wrong port numbers"
      new_inports <- pure $ M.elems new_inports -- sorted
      -- This *replaces* the earlier 'src' node with the same name, just updating the ports
      req $ AddNode src (BratNode Source [] (map (second $ akindType Braty) (ss ++ new_inports)))
      -- Now make the box. This has inputs *only* for the captured variables
      -- (not the arguments - those are supplied in addition to the box when it's eval'd)
      (box_node,_,[thunk],_) <- next (name ++ "_thunk") (src :>>: tgt) (vctx,B0) new_inports [("thunk", Right (VFun ?my B0 (ss :-> ts)))]
      -- Finally, wire captured values into box
      forM (concat inner_outer_srcs) (
        \((NamedPort {end=Ex _ n, portName=p}, ty), osrc) -> case ty of
          Right ty -> wire (osrc, ty, NamedPort {end=In box_node (n-n_args), portName=p})
          Left _ -> pure ()
        )
      pure (thunk, bres)

uncons :: Modey m -> ValueType m -> Maybe (ValueType m, ValueType m)
uncons Kerny (Of ty n) = case valMatch n (VPNum (NP1Plus NPVar)) of
  Right (B0 :< m) -> pure (ty, Of ty m)
  _ -> Nothing
uncons Braty (TList ty) = Just (ty, TList ty)
uncons Braty (TVec ty n) = case valMatch n (VPNum (NP1Plus NPVar)) of
  Right (B0 :< m) -> pure (ty, TVec ty m)
  _ -> Nothing
uncons Braty (TCons x xs) = Just (x, xs)
uncons _ _ = Nothing

-- Evaluate either mode's BinderType
evalBinder :: Modey m -> BinderType m -> Checking (BinderType m)
evalBinder Kerny sty = evSTy sty
evalBinder Braty (Right ty) = Right <$> evTy ty
evalBinder Braty (Left k) = pure (Left k)

evalRowElem :: Modey m -> (a, BinderType m) -> Checking (a, BinderType m)
evalRowElem Braty (p, Right ty) = (p,) . Right <$> evTy ty
evalRowElem Braty (p, Left k) = pure (p, Left k)
evalRowElem Kerny (p, ty) = (p,) <$> evSTy ty

-- This should be a row of Srcs, generated by next, rather than a
-- signature to ensure that all Inx's are instantiated
evalSrcRow :: Modey m -> [(Src, BinderType m)] -> Checking [(Src, BinderType m)]
evalSrcRow m = traverse (evalRowElem m)

evalTgtRow :: Modey m -> [(Tgt, BinderType m)] -> Checking [(Tgt, BinderType m)]
evalTgtRow m = traverse (evalRowElem m)
