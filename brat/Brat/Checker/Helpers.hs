{-# LANGUAGE AllowAmbiguousTypes #-}

module Brat.Checker.Helpers where

import Brat.Checker.Monad (Checking, CheckingSig(..), captureOuterLocals, err, typeErr, kindArgRows, defineEnd, throwLeft, isSkolem, mkYield)
import Brat.Checker.Types
import Brat.Error (ErrorMsg(..))
import Brat.Eval (eval, EvMode(..), kindType)
import Brat.FC (FC)
import Brat.Graph (Node(..), NodeType(..))
import Brat.Naming (Name)
import Brat.Syntax.Common
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Simple
import Brat.Syntax.Port (ToEnd(..))
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Hasochism
import Util (log2)

import Control.Monad.Freer
import Control.Arrow ((***))
import Data.Functor ((<&>))
import Data.List (intercalate)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding (last)

simpleCheck :: Modey m -> Val Z -> SimpleTerm -> Checking ()
simpleCheck my ty tm = case (my, ty) of
  (Braty, VApp (VPar e) _) -> do
    isHope <- req AskHopeSet <&> M.member e
    if isHope then
      case tm of
        Float _ -> defineEnd e TFloat
        Text _ -> defineEnd e TText
        Num n | n < 0 -> defineEnd e TInt
        Num _ -> typeErr $ "Can't determine whether Int or Nat: " ++ show tm
    else isSkolem e >>= \case
      True -> throwLeft $ helper Braty ty tm
      False -> mkYield "simpleCheck" (S.singleton e) >> simpleCheck Braty ty tm
  _ -> throwLeft $ helper my ty tm
 where
  helper :: Modey m -> Val Z -> SimpleTerm -> Either ErrorMsg ()
  helper Braty TNat (Num n) | n >= 0 = pure ()
  helper Braty TInt (Num _) = pure ()
  helper Braty TFloat (Float _) = pure ()
  helper Braty TText (Text _) = pure ()
  helper _ ty tm = Left $ TypeErr $ unwords
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
  portNameExists Braty p (REx (p', _) ro)
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
  pull1Port p [] = fail $ "Port not found: " ++ p ++ " in " ++ showFn types
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
      -> NodeType m
      -> (Semz i, Some Endz)
      -> Ro m i j -- Inputs and Outputs use de Bruijn indices
      -> Ro m j k
      -> Checking (Name, Unders m Chk, Overs m UVerb, (Semz k, Some Endz))
anext str th vals0 ins outs = anext' str th vals0 ins outs $ case th of
  Source -> True
  _ -> False

anext' :: forall m i j k
       . EvMode m
      => String
      -> NodeType m
      -> (Semz i, Some Endz)
      -> Ro m i j -- Inputs and Outputs use de Bruijn indices
      -> Ro m j k
      -> Bool -- whether outports are skolem consts (will never be defined), inports never are
      -> Checking (Name, Unders m Chk, Overs m UVerb, (Semz k, Some Endz))
anext' str th vals0 ins outs skol = do
  node <- req (Fresh str) -- Pick a name for the thunk
  -- Use the new name to generate Ends with which to instantiate types
  (unders, vals1) <- endPorts node InEnd In 0 vals0 ins
  (overs, vals2)  <- endPorts node ExEnd Ex 0 vals1 outs
  () <- sequence_ $
        [ declareTgt tgt (modey @m) ty | (tgt, ty) <- unders ] ++
        [ req (Declare (ExEnd (end src)) (modey @m) ty skol) | (src, ty) <- overs ]

  let inputs  = [ (portName p, biType @m ty) | (p, ty) <- unders ]
  let outputs = [ (portName p, biType @m ty) | (p, ty) <- overs  ]

  () <- req (AddNode node (mkNode (modey @m) th inputs outputs))
  pure (node, unders, overs, vals2)

mkNode :: forall m. Modey m -> NodeType m
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
         -> (Semz i, Some Endz)
         -> Ro m i j
         -> Checking ([(NamedPort port, BinderType m)], (Semz j, Some Endz))
endPorts _ _ _ _ stuff R0 = pure ([], stuff)
endPorts node port2End mkPort n (ga, ez) (RPr (p,ty) ro) = do
  ty <- eval ga ty
  (row, stuff) <- endPorts node port2End mkPort (n + 1) (ga, ez) ro
  pure ((NamedPort (mkPort node n) p, tyBinder @m ty):row, stuff)
endPorts node port2End mkPort n (ga, Some (ny :* endz)) (REx (p, k) ro) = do
  let port = mkPort node n
  let end = port2End port
  (row, stuff) <- endPorts node port2End mkPort (n + 1)
                  (ga :<< SApp (SPar end) B0, Some (Sy ny :* (endz :<< end))) ro
  pure ((NamedPort port p, Left k):row, stuff)
next :: String -> NodeType Brat -> (Semz i, Some Endz)
     -> Ro Brat i j
     -> Ro Brat j k
     -> Checking (Name, Unders Brat Chk, Overs Brat UVerb, (Semz k, Some Endz))
next = let ?my = Braty in anext

knext :: String -> NodeType Kernel -> (Semz i, Some Endz)
      -> Ro Kernel i i
      -> Ro Kernel i i
      -> Checking (Name, Unders Kernel Chk, Overs Kernel UVerb, (Semz i, Some Endz))
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
  v -> do
    h <- req AskHopeSet
    case v of
      VApp (VPar e) _ | M.member e h -> mkYield "getThunks" (S.singleton e) >> getThunks Braty row
      _ -> typeErr $ "Force called on non-thunk: " ++ show v
getThunks Kerny row@((src, Right ty):rest) = eval S0 ty >>= \case
  (VFun Kerny (ss :->> ts)) -> do
    (node, unders, overs, _) <- let ?my = Kerny in anext "" (Splice (end src)) (S0, Some (Zy :* S0)) ss ts
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
defineSrc src v = defineEnd (ExEnd (end src)) v

defineTgt :: Tgt -> Val Z -> Checking ()
defineTgt tgt v = defineEnd (InEnd (end tgt)) v

declareTgt :: Tgt -> Modey m -> BinderType m -> Checking ()
declareTgt tgt my ty = req (Declare (InEnd (end tgt)) my ty False)

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
      (_,_,[thunk],_) <- next (name ++ "_thunk") (Box src tgt) (S0, Some (Zy :* S0))
                                R0 (RPr ("thunk", VFun Kerny cty) R0)
      bres <- body (overs, unders)
      pure (thunk, bres)
    (Braty, body) -> do
      (node, [], [thunk], _) <- next (name ++ "_thunk") (Box src tgt) (S0, Some (Zy :* S0))
                                     R0 (RPr ("thunk", VFun ?my cty) R0)
      bres <- (captureOuterLocals node $ body (overs, unders))
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

rowToRo :: ToEnd t => Modey m -> [(String, t, BinderType m)] -> Stack Z End i -> Checking (Some ((Ro m i) :* Stack Z End))
rowToRo _ [] stk = pure $ Some (R0 :* stk)
rowToRo Kerny ((p, _, ty):row) S0 = do
  ty <- eval S0 ty
  rowToRo Kerny row S0 >>= \case
    Some (ro :* stk) -> pure . Some $ ((RPr (p, changeVar (ParToInx (AddZ Zy) S0) ty) ro)) :* stk
rowToRo Kerny _ (_ :<< _) = err $ InternalError "rowToRo - no binding allowed in kernels"

rowToRo Braty ((p, _, Right ty):row) endz = do
  ty <- eval S0 ty
  rowToRo Braty row endz >>= \case
    Some (ro :* stk) -> pure . Some $ (RPr (p, changeVar (ParToInx (AddZ (stackLen endz)) endz) ty) ro) :* stk
rowToRo Braty ((p, tgt, Left k):row) endz = rowToRo Braty row (endz :<< toEnd tgt) >>= \case
  Some (ro :* stk) -> pure . Some $ (REx (p, k) ro) :* stk

roToTuple :: Ro m Z Z -> Val Z
roToTuple R0 = TNil
roToTuple (RPr (_, ty) ro) = TCons ty (roToTuple ro)
roToTuple (REx _ ro) = case ro of
  _ -> error "the impossible happened"

-- Low hanging fruit that we can easily do to our normal forms of numbers
runArith :: NumVal (VVar Z) -> ArithOp -> NumVal (VVar Z) -> Maybe (NumVal (VVar Z))
runArith (NumValue upl grol) Add (NumValue upr gror)
-- We can add when one of the sides is a constant...
 | Constant0 <- grol = pure $ NumValue (upl + upr) gror
 | Constant0 <- gror = pure $ NumValue (upl + upr) grol
 -- ... or when Fun00s are the same
 | grol == gror = pure $ NumValue (upl + upr) grol
runArith (NumValue upl grol) Sub (NumValue upr gror)
-- We can subtract when the rhs is a constant...
 | Constant0 <- gror, upl >= upr = pure $ NumValue (upl - upr) grol
 -- ... or when the Fun00s are the same...
 | grol == gror, upl >= upr = pure $ NumValue (upl - upr) Constant0
 -- ... or we have (c + 2^(k + 1) * x) - (c' + 2^k * x)
 | StrictMonoFun (StrictMono k m) <- grol
 , StrictMonoFun (StrictMono k' m') <- gror
 , m == m'
 , k == (k' + 1)
 , upl >= upr = pure $ NumValue (upl - upr) gror
runArith (NumValue upl grol) Mul (NumValue upr gror)
 -- We can multiply two constants...
 | Constant0 <- grol
 , Constant0 <- gror = pure $ NumValue (upl * upr) grol
 -- ... or we can multiply by a power of 2
 | Constant0 <- grol
 , StrictMonoFun (StrictMono k' m) <- gror
 , Just k <- log2 upl = pure $ NumValue (upl * upr) (StrictMonoFun (StrictMono (k + k') m))
 | Constant0 <- gror
 , StrictMonoFun (StrictMono k' m) <- grol
 , Just k <- log2 upr = pure $ NumValue (upl * upr) (StrictMonoFun (StrictMono (k + k') m))
runArith (NumValue upl grol) Pow (NumValue upr gror)
 -- We can take constants to the power of constants...
 | Constant0 <- grol
 , Constant0 <- gror = pure $ NumValue (upl ^ upr) Constant0
 -- ... or we can take a constant to the power of a NumValue if the constant
 -- is 2^(2^c)
 | Constant0 <- grol
 , Just l <- log2 upl
 , Just k <- log2 l
 , StrictMonoFun (StrictMono k' mono) <- gror
 -- 2^(2^k) ^ (upr + (2^k' * mono))
 -- (2^(2^k))^upr * (2^(2^k))^(2^k' * mono)
 -- 2^(2^k * upr) * 2^(2^k * (2^k' * mono))
 -- 2^(2^k * upr) * (1 + 2^(2^k * (2^k' * mono)) - 1)
 -- 2^(2^k * upr) + 2^(2^k * upr) * (2^(2^k * (2^k' * mono)) - 1)
 -- 2^(2^k * upr) + 2^(2^k * upr) * (full(2^k * (2^k' * mono))
 -- 2^(2^k * upr) + 2^(2^k * upr) * (full(2^(k + k') * mono))
 = pure $ NumValue (upl ^ upr) (StrictMonoFun (StrictMono (l * upr) (Full (StrictMono (k + k') mono))))
runArith _ _ _ = Nothing

buildArithOp :: ArithOp -> Checking ((Tgt, Tgt), Src)
buildArithOp op = do
  (_, [(lhs,_), (rhs,_)], [(out,_)], _) <- next "" (ArithNode op) (S0, Some (Zy :* S0)) (RPr ("lhs", TNat) (RPr ("rhs", TNat) R0)) (RPr ("value", TNat) R0)
  pure ((lhs, rhs), out)

buildConst :: SimpleTerm -> Val Z -> Checking Src
buildConst tm ty = do
  (_, _, [(out,_)], _) <- next "" (Const tm) (S0, Some (Zy :* S0)) R0 (RPr ("value", ty) R0)
  pure out
