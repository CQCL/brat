{-# LANGUAGE
ConstraintKinds,
FlexibleContexts,
MultiParamTypeClasses
#-}

module Brat.Checker (check
                    ,run
                    ,VEnv
                    ,Checking
                    ,Graph
                    ,Modey(..)
                    ,Node
                    ,CheckingSig(..)
                    ,TypedHole(..)
                    ,wrapError
                    ,next, knext
                    ,localFC
                    ,emptyEnv
                    ,checkInputs, checkOutputs, checkThunk
                    ,CheckConstraints
                    ,TensorOutputs(..)
                    ,kindCheck, kindCheckRow
                    ) where

import Control.Monad (foldM)
import Control.Monad.Freer
import Control.Monad.State (StateT, runStateT, get, put, lift)
import Data.Functor (($>))
-- import Data.List (filter, intercalate, transpose)
import qualified Data.Map as M
import Data.Traversable (for)
import Prelude hiding (filter)

import Brat.Checker.Helpers
import Brat.Checker.Monad
import Brat.Checker.Quantity
import Brat.Checker.Types
import Brat.Constructors
import Brat.Error
import Brat.Eval (Eval(eval), apply)
import Brat.FC hiding (end)
import Brat.Graph
import Brat.Naming
-- import Brat.Search
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Util

mergeEnvs :: [Env a] -> Checking (Env a)
mergeEnvs = foldM combineDisjointEnvs M.empty

emptyEnv :: Env a
emptyEnv = M.empty

singletonEnv :: (?my :: Modey m) => String -> (Src, BinderType m) -> Env (EnvData m)
singletonEnv x input@(p, ty) = case ?my of
  Braty -> M.singleton (plain x) [(p, ty)]
  Kerny -> let q = if copyable ty then Tons else One
           in  M.singleton (plain x) (q, input)


class TensorOutputs d where
  tensor :: d -> d -> d

instance TensorOutputs () where
  tensor () () = ()

instance TensorOutputs [(Src, KindOr a)] where
 tensor ss ts = ss <> ts

instance TensorOutputs [(Src, SValue)] where
 tensor ss ts = ss <> ts

class CombineInputs d where
  combine :: d -> d -> d

instance CombineInputs () where
  combine () () = ()

instance CombineInputs [(Tgt, a)] where
  combine = (++)

type CheckConstraints m k =
  (Show (ValueType m)
  ,Show (BinderType m)
  ,DeBruijn (BinderType m)
  ,TensorOutputs (Outputs m Syn)
  ,TensorOutputs (Outputs m Chk)
  ,CombineInputs (Inputs m k)
  ,CombineInputs (Inputs m Noun)
  ,CombineInputs (Inputs m UVerb)
  ,CombineInputs (Inputs m KVerb)
  )

checkWire :: Modey m
          -> WC (Term d k) -- The term (for error reporting)
          -> Bool -- Is the "Src" node the expected one?
          -> (Src, BinderType m)
          -> (Tgt, BinderType m)
          -> Checking ()
checkWire Braty _ outputs (dangling, Left ok) (hungry, Left uk) = do
  throwLeft $ if outputs
    then kindEq ok uk
    else kindEq uk ok
  defineTgt hungry (endVal ok (ExEnd (end dangling)))
  wire (dangling, kindType ok, hungry)
checkWire Braty (WC fc tm) outputs (dangling, o) (hungry, u) = localFC fc $ do
  let ot = binderToValue Braty o
  let ut = binderToValue Braty u
  if outputs
    then typeEq (show tm) (Star []) ot ut
    else typeEq (show tm) (Star []) ut ot
  wire (dangling, ot, hungry)
checkWire Kerny (WC fc tm) outputs (dangling, ot) (hungry, ut) = localFC fc $ do
  if outputs
    then stypeEq (show tm) ot ut
    else stypeEq (show tm) ut ot
  kwire (dangling, ot, hungry)

checkInputs :: (CheckConstraints m KVerb, ?my :: Modey m)
            => WC (Term d KVerb)
            -> [(Src, BinderType m)] -- Expected
            -> [(Tgt, BinderType m)] -- Actual
            -> Checking [(Src, BinderType m)]
checkInputs _ overs [] = pure overs
checkInputs tm@(WC fc _) (o:overs) (u:unders) = localFC fc $ do
  wrapError (addRowContext ?my (o:overs) (u:unders)) $ checkWire ?my tm False o u
  checkInputs tm overs unders
 where
  addRowContext :: Show (BinderType m)
              => Modey m
              -> [(Src, BinderType m)] -- Expected
              -> [(Tgt, BinderType m)] -- Actual
              -> Error -> Error
  addRowContext _ as bs (Err fc (TypeMismatch tm _ _))
   = Err fc $ TypeMismatch tm (showRow as) (showRow bs)
  addRowContext _ _ _ e = e
checkInputs tm [] unders = typeErr $ "No overs but unders: " ++ show unders ++ " for " ++ show tm

checkOutputs :: (CheckConstraints m k, ?my :: Modey m)
             => WC (Term Syn k)
             -> [(Tgt, BinderType m)] -- Expected
             -> [(Src, BinderType m)] -- Actual
             -> Checking [(Tgt, BinderType m)]
checkOutputs _ unders [] = pure unders
checkOutputs tm@(WC fc _) (u:unders) (o:overs) = localFC fc $ do
  wrapError (addRowContext ?my (u:unders) (o:overs)) $ checkWire ?my tm True o u
  checkOutputs tm unders overs
 where
  addRowContext :: Show (BinderType m)
              => Modey m
              -> [(Tgt, BinderType m)] -- Expected
              -> [(Src, BinderType m)] -- Actual
              -> Error -> Error
  addRowContext _ as bs (Err fc (TypeMismatch tm _ _))
   = Err fc $ TypeMismatch tm (showRow as) (showRow bs)
  addRowContext _ _ _ e = e
checkOutputs tm [] overs = typeErr $ "No unders but overs: " ++ show overs ++ " for " ++ show tm

checkThunk :: (?my :: Modey m, CheckConstraints m UVerb)
           => String
           -> Bwd Value
           -> [(PortName, BinderType m)] -> [(PortName, BinderType m)]
           -> WC (Term Chk UVerb)
           -> Checking Src
checkThunk name vctx ss ts tm = do
  ((dangling,_), thOvers, thUnders) <- makeBox name vctx ss ts
  (((), ()), (emptyOvers, emptyUnders)) <- check tm (thOvers, thUnders)
  ensureEmpty "thunk leftovers" emptyOvers
  ensureEmpty "thunk leftunders" emptyUnders
  pure dangling

check :: (CheckConstraints m k, TensorOutputs (Outputs m d), ?my :: Modey m)
      => WC (Term d k)
      -> ChkConnectors m d k
      -> Checking (SynConnectors m d k
                  ,ChkConnectors m d k)
check (WC fc tm) conn = localFC fc (check' tm conn)

check' :: (CheckConstraints m k, TensorOutputs (Outputs m d), ?my :: Modey m)
       => Term d k
       -> ChkConnectors m d k
       -> Checking (SynConnectors m d k
                   ,ChkConnectors m d k) -- rightovers
check' Empty tys = pure (((), ()), tys)
check' (s :|: t) tys = do
  -- in Checking mode, each LHS/RHS removes its wires+types from the ChkConnectors remaining
  ((ins, outs), tys)  <- check s tys
  ((ins', outs'), tys) <- check t tys
  -- in Synthesizing mode, instead here we join together the outputs, and the inputs
  pure ((combine ins ins', tensor outs outs'), tys)
check' (s :-: t) (overs, unders) = do
  -- s is Syn, t is a UVerb
  ((ins, overs), (rightovers, ())) <- check s (overs, ())
  (((), outs), (emptyOvers, rightunders)) <- check t (overs, unders)
  ensureEmpty "composition overs" emptyOvers
  pure ((ins, outs), (rightovers, rightunders))
check' (binder :\: body) (overs, unders) = do
  (ext, overs, _) <- abstract (B0, 0) overs (unWC binder)
  (sycs, ((), unders)) <- localEnv ext $ check body ((), unders)
  pure (sycs, (overs, unders))
check' (Pull ports t) (overs, unders) = do
  unders <- pullPortsRow ports unders
  check t (overs, unders)
check' (t ::: outs) (overs, ()) | Braty <- ?my = do
  -- Check that the annotation is a valid row
  sig <- kindCheckRow outs
  (_, hungries, danglies, _) <- next "id" Id (B0,B0) sig sig
  ((), leftOvers) <- noUnders $ check t (overs, hungries)
  pure (((), danglies), (leftOvers, ()))
check' (Emb t) (overs, unders) = do
  ((ins, outs), (overs, ())) <- check t (overs, ())
  unders <- checkOutputs t unders outs
  pure ((ins, ()), (overs, unders))
check' (Th t) ((), u@(hungry, ty):unders) = ((?my,) <$> evalBinder ?my ty) >>= \case
  (Braty, ty) -> do
    ty <- evalBinder Braty ty
    case ty of
      Right ty@(VFun Braty ctx (ss :-> ts)) -> let ?my = Braty in
        checkThunk "thunk" ctx ss ts t >>= wire . (,ty, hungry)
      Right ty@(VFun Kerny ctx (ss :-> ts)) -> let ?my = Kerny in
        checkThunk "thunk" ctx ss ts t >>= wire . (,ty, hungry)
      Left (Star args) -> kindCheck [(hungry, Star args)] (Th t) $> ()
      _ -> err . ExpectedThunk "" $ showRow (u:unders)
    pure (((), ()), ((), unders))
  (Kerny, _) -> err . ThunkInKernel $ show (Th t)
check' (TypedTh t) ((), ()) = case ?my of
  -- the thunk itself must be Braty
  Kerny -> err . ThunkInKernel $ show (TypedTh t)
  Braty -> do
    -- but the computation in it could be either Brat or Kern
    brat <- catchErr $ check t ((), ())
    kern <- catchErr $ let ?my = Kerny in check t ((), ())
    case (brat, kern) of
      (Left e, Left _) -> req $ Throw e -- pick an error arbitrarily
      -- I don't believe that there is any syntax that could synthesize
      -- both a classical type and a kernel type, but just in case:
      -- (pushing down Emb(TypedTh(v)) to Thunk(Emb+Forget(v)) would help in Checkable cases)
      (Right _, Right _) -> typeErr "TypedTh could be either Brat or Kernel"
      (Left _, Right (conns, ((), ()))) -> let ?my = Kerny in createThunk conns
      (Right (conns, ((), ())), Left _) -> createThunk conns
 where
  createThunk :: (CheckConstraints m Noun, ?my :: Modey m)
              => SynConnectors m Syn KVerb
              -> Checking (SynConnectors Brat Syn Noun
                          ,ChkConnectors Brat Syn Noun)
  createThunk (ins, outs) = do
    (thunkOut, thOvers, thUnders) <- makeBox "thunk" B0 (rowToSig ins) (rowToSig outs)
    -- if these ensureEmpty's fail then its a bug!
    () <- checkInputs t thOvers ins >>= ensureEmpty "TypedTh inputs"
    () <- checkOutputs t thUnders outs >>= ensureEmpty "TypedTh outputs"
    pure (((), [thunkOut]), ((), ()))
check' (Force th) ((), ()) = do
  (((), outs), ((), ())) <- let ?my = Braty in check th ((), ())
  -- pull a bunch of thunks (only!) out of here
  (_, thInputs, thOutputs) <- getThunks ?my outs
  pure ((thInputs, thOutputs), ((), ()))
check' (Forget kv) (overs, unders) = do
  ((ins, outs), ((), rightUnders)) <- check kv ((), unders)
  leftOvers <- checkInputs kv overs ins
  pure (((), outs), (leftOvers, rightUnders))
check' (Var x) ((), ()) = (, ((), ())) . ((),) <$> case ?my of
  Braty -> vlup x
  Kerny -> req (KLup x) >>= \case
    Just (p, ty) -> pure [(p, ty)]
    Nothing -> err $ KVarNotFound (show x)
check' (fun :$: arg) (overs, unders) = do
  ((ins, outputs), ((), leftUnders)) <- check fun ((), unders)
  ((argIns, ()), (leftOvers, argUnders)) <- check arg (overs, ins)
  ensureEmpty "leftover function args" argUnders
  pure ((argIns, outputs), (leftOvers, leftUnders))
check' (Let abs x y) conn = do
  (((), dangling), ((), ())) <- check x ((), ())
  env <- abstractAll dangling (unWC abs)
  localEnv env $ check y conn
check' (NHole name) ((), unders) = req AskFC >>= \fc -> case ?my of
  Kerny -> do
    req $ LogHole $ NKHole name fc ((), unders)
    pure (((), ()), ((), []))
  Braty -> do
    suggestions <- getSuggestions fc
    req $ LogHole $ NBHole name fc suggestions ((), unders)
    pure (((), ()), ((), []))
   where
    getSuggestions :: FC -> Checking [String]
    getSuggestions _ = pure []
-- TODO: Fix this
{-
    do
      matches <- findMatchingNouns
      let sugg = transpose [ [ tm | tm <- vsearch fc ty ]
                           | (_, ty) <- unders]
      let ms = intercalate ", " . fmap show <$> matches
      let ss = intercalate ", " . fmap show <$> sugg
      pure $ take 5 (ms ++ ss)

    findMatchingNouns :: Checking [[UserName]]
    findMatchingNouns = do
      -- TODO
      pure []

      let tys = snd <$> unders
      env <- req AskVEnv
      let matches = transpose $
            [ [ (nm, src) | (src, _) <- stuff ]
            | (nm, stuff) <- M.assocs env
            , and (zipWith (==) tys (snd <$> stuff))
            ]
      pure $ fmap fst <$> matches
-}

check' (VHole name) (overs, unders) = do
  fc <- req AskFC
  req $ LogHole $ case ?my of
    Braty -> VBHole name fc (overs, unders)
    Kerny -> VKHole name fc (overs, unders)
  pure (((), ()), ([], []))
-- TODO: Better error message
check' tm@(Con _ _) ((), []) = typeErr $ "No type to check " ++ show tm ++ " against"
check' tm@(Con vcon arg) ((), ((hungry, ty):unders)) = case (?my, ty) of
  (Braty, Left k) -> do
    (_, leftOvers) <- kindCheck [(hungry, k)] (Con vcon arg)
    ensureEmpty "kindCheck leftovers" leftOvers
    pure (((), ()), ((), unders))
  (Braty, Right ty) -> do
    VCon tycon tyargs <- evTy ty
    (pats, args) <- clup vcon tycon
    -- Look for vectors to produce better error messages for mismatched lengths
    wrap <- detectVecErrors vcon tycon tyargs pats ty (Left tm)
    env <- throwLeft $ valMatches tyargs pats
    (_, argUnders, [(dangling, _)], _) <- anext (show vcon) (Constructor vcon) (env, B0)
                                          args [("value", Right ty)]
    (((), ()), ((), leftUnders)) <- wrapError wrap $ check arg ((), argUnders)
    ensureEmpty "con unders" leftUnders
    wire (dangling, ty, hungry)
    pure (((), ()), ((), unders))
  (Kerny, _) -> do
    ty <- evSTy ty
    outerFC <- req AskFC
    case (ty, vcon, unWC arg) of
      (Of ty (VNum n), PrefixName [] "nil", Empty) -> case numMatch B0 n NP0 of
        Right B0 -> do
          (_, _, [(dangling, _)], _) <- knext (show vcon) (Constructor vcon) (B0,B0)
                                        [] [("value", Of ty (VNum n))]
          kwire (dangling, Of ty (VNum n), hungry)
          pure (((), ()), ((), unders))
        Left _ -> err $ VecLength (show tm) (show $ Of ty (VNum n)) (show n) (Length 0)
      (Of ty (VNum succN), PrefixName [] "cons", _) -> case numMatch B0 succN (NP1Plus NPVar) of
        Right (B0 :< (VNum n)) -> do
          let tailTy = Of ty (VNum succN)
          (_, argUnders, [(dangling, _)], _) <-
            anext (show vcon) (Constructor vcon) (B0,B0)
            [("head", ty), ("tail", Of ty (VNum n))]
            [("value", tailTy)]
          (((), ()), ((), [])) <- wrapError (consError outerFC (Left tm) (show tailTy) succN) $
                                  check arg ((), argUnders)
          kwire (dangling, Of ty (VNum succN), hungry)
          pure (((), ()), ((), unders))
        Left _ -> err $ VecLength (show tm) (show $ Of ty (VNum succN)) (show succN) (LongerThan 0)
check' (C cty) ((), ((hungry, ty):unders)) = case (?my, ty) of
  (Braty, Left k) -> do
    (_, leftOvers) <- kindCheck [(hungry, k)] (C cty)
    ensureEmpty "kindCheck leftovers" leftOvers
    pure (((), ()), ((), unders))
  _ -> typeErr $ "Ill-kinded function type: " ++ show cty
check' (Simple tm) ((), ((hungry, ty):unders)) = ((?my,tm,) <$> evalBinder ?my ty) >>= \case
  (Braty, tm, Right ty@(VCon (PrefixName [] c) []))
   | valid tm c -> do
      (_, _, [(dangling, _)], _) <- next "" (Const tm) (B0,B0) [] [("value", Right ty)]
      wire (dangling, ty, hungry)
      pure (((), ()), ((), unders))
  (Kerny, Bool _, Bit) -> do
    (_,_,[(dangling, _)],_) <- knext "" (Const tm) (B0,B0) [] [("value", Bit)]
    kwire (dangling, Bit, hungry)
    pure (((), ()), ((), unders))
  _ -> typeErr $ "Expected something of type `" ++ show ty ++ "` but got `" ++ show tm ++ "`"
 where
  valid :: SimpleTerm -> String -> Bool
  valid (Bool _) "Bool" = True
  valid (Num _) "Int" = True
  valid (Num n) "Nat" = n >= 0
  valid (Text _) "String" = True
  valid (Float _) "Float" = True
  valid _ _ = False
check' tm _ = error $ "check' " ++ show tm

-- Check a type against a row of kinds, and evaluate it
-- define the ends from unders when appropriate
-- N.B. Wires should be declared before they arrive here, we're going to define them here
kindCheck :: [(Tgt, TypeKind)] -- Kinds checking against
          -> Term Chk Noun     -- The type to scrutinise
          -> Checking ([Value] -- The values produced evaluating term arguments
                      ,[(Tgt, TypeKind)]) -- Leftovers (rightunders)
kindCheck unders Empty = pure ([], unders)
kindCheck [] tm = err $ InternalError $  "kindCheck called with empty unders for " ++ show tm
kindCheck unders (a :|: b) = do
  (vs, unders) <- kindCheck unders (unWC a)
  (vs', unders) <- kindCheck unders (unWC b)
  pure (vs <> vs', unders)
kindCheck _ (Pull _ _) = err $ Unimplemented "Port pulling in kinds" [] -- FIXME
kindCheck ((hungry, k@(Star [])):unders) (Con c arg) = req (TLup k c) >>= \case
  -- This must be either a type constructor...
  Just args -> do
    (_, argUnders, [(dangling, _)], _) <- next (show c) (Constructor c) (B0,B0)
                                          [ (p, Left k) | (p, k) <- args ]
                                          [("value", Left (Star []))]
    let kindArgs = [ (tgt, k) | (tgt, Left k) <- argUnders ]
    -- recurse first so we Define the necessary argUnders
    (_, argUnders) <- kindCheck kindArgs (unWC arg)
    ensureEmpty "kindCheck unders" argUnders
    -- now evVa can pick up the definitions
    value <- evVa $ VCon c [ endVal k (InEnd (end tgt)) | (tgt, k) <- kindArgs ]
    defineTgt hungry value
    defineSrc dangling value
    wire (dangling, kindType k, hungry)
    pure ([value],unders)
  -- ... or a type alias
  Nothing -> req (ALup c) >>= \case
    Just (ks, pats, alias) -> do
      let argIO = zip names (pats $> Left (Star []))
      (_, argUnders, _, _) <- next "" Hypo (B0,B0) argIO argIO
      (args, []) <- kindCheck (zip (fst <$> argUnders) (snd <$> ks)) (unWC arg)
      args <- throwLeft $ valMatches args pats
      val <- foldM (apply (req . ELup)) alias args
      defineTgt hungry val
      pure ([val], unders)
    Nothing -> typeErr $ "Can't find type constructor or type alias " ++ show c
kindCheck ((hungry, Star []):unders) (C funTy) = do
  funTy <- kindCheckRow funTy
  let val = VFun Braty B0 funTy
  defineTgt hungry val
  pure ([val], unders)
kindCheck ((hungry, Star []):unders) (K (R ss) (R ts)) = do
  -- N.B. Kernels can't bind so we don't need to pass around a stack of ends
  ss <- skindCheckRow ss
  ts <- skindCheckRow ts
  let val = VFun Kerny B0 (ss :-> ts)
  defineTgt hungry val
  pure ([val], unders)
kindCheck ((hungry, Star args):unders) (Th (WC _ (xs :\: body))) = do
  (_, _, kovers, (_, ends)) <- next "" Hypo (B0,B0) [] [(p, Left k) | (p, k) <- args]
  (ext, (argEnds, _)) <- let ?my = Braty in abstractAll' kovers (unWC xs)
  (_, [(hhungry, Left k)], [], _) <- next "" Hypo (B0,B0) [("type", Left (Star []))] []
  let body' = changeVar (InxToPar argEnds) 0 (unWC body)
  ([vbody], emptyUnders) <- localVEnv ext $ kindCheck [(hhungry, k)] body'
  ensureEmpty "kindCheck unders" emptyUnders
  vbody <- evVa vbody
  let val = lambdify ends (changeVar (ParToInx ends) 0 vbody)
  defineTgt hungry val
  pure ([val], unders)
 where
  lambdify :: Bwd a -> Value -> Value
  lambdify B0 v = v
  lambdify (zx :< _) v = lambdify zx (VLam B0 v)
kindCheck ((hungry, k):unders) (Emb (WC _ (Par e))) = do
  Just k' <- req (EndKind e)
  throwLeft $ kindEq k k'
  val <- evVa $ endVal k e
  defineTgt hungry val
  pure ([val], unders)
kindCheck unders (Emb (WC _ (Var v))) = vlup v >>= f unders
 where
  f :: [(Tgt, TypeKind)] -> [(Src, BinderType Brat)]
    -> Checking ([Value], [(Tgt, TypeKind)])
  f unders [] = pure ([], unders)
  f [] _ = typeErr "Empty unders"
  f  ((hungry, k'):us) ((dangling, Left k):xs) = do
    throwLeft $ kindEq k k'
    wire (dangling, kindType k, hungry)
    value <- evVa (endVal k (ExEnd (end dangling)))
    defineTgt hungry value
    (vs, leftUnders) <- f us xs
    pure (value:vs, leftUnders)
-- TODO: Add other operations on numbers
kindCheck ((hungry, Nat):unders) (Simple (Num n)) | n >= 0 = do
  (_, _, [(dangling, _)], _) <- next "" (Const (Num n)) (B0,B0) [] [("value", Left Nat)]
  let value = VNum (nConstant n)
  defineTgt hungry value
  defineSrc dangling value
  wire (dangling, TNat, hungry)
  pure ([value], unders)
kindCheck ((hungry, Nat):unders) (Con c arg)
 | Just (_, f) <- M.lookup c natConstructors = do
     -- All nat constructors have one input and one output
     (_, [(chungry,_)], [(cdangling,_)], _) <- next (show c) (Constructor c) (B0,B0)
                                               [("in", Left Nat)]
                                               [("out", Left Nat)]
     wire (cdangling, TNat, hungry)
     ([VNum nv], us) <- kindCheck [(chungry, Nat)] (unWC arg)
     ensureEmpty "kindCheck unders" us
     v <- eval (req . ELup) B0 (VNum (f nv))
     defineSrc cdangling v
     defineTgt hungry v
     pure ([v], unders)
kindCheck unders tm = err $ Unimplemented "kindCheck" [showRow unders, show tm]

-- kindCheck, but for kernel types
-- Note that all dependency happens in classical terms,
-- so we only really care about the index in `Of`
skindCheck :: [(Tgt, TypeKind)]
           -> SType' (Term Chk Noun)
           -> Checking ([SValue], [(Tgt, TypeKind)])
skindCheck ((_, Star []):unders) (Q q) = pure ([Q q], unders)
skindCheck ((_, Star []):unders) Bit = pure ([Bit], unders)
skindCheck ((_, Star []):unders) (Of sty n) = do
  nm <- req (Fresh "")
  let signal = NamedPort (In nm 0) "type"
  declareTgt signal (Star [])
  ([vsty], emptyUnders) <- skindCheck [(signal, Star [])] sty
  ensureEmpty "skindCheck unders" emptyUnders

  nm2 <- req (Fresh "")
  let size = NamedPort (In nm2 0) "value"
  declareTgt size Nat
  ([vn], emptyUnders) <- kindCheck [(size, Nat)] n
  ensureEmpty "kindCheck unders" emptyUnders
  pure ([Of vsty vn], unders)
skindCheck ((_, Star []):unders) (Rho (R row))
  = (,unders) . (:[]) . Rho . R <$> skindCheckRow row

skindCheckRow :: [(PortName, SType' (Term Chk Noun))] -> Checking [(PortName, SValue)]
skindCheckRow xs = do
  node <- req (Fresh "")
  for (zip xs [0..]) $ \((p, sty), i) -> do
    let tgt = NamedPort (In node i) p
    declareTgt tgt (Star [])
    ([v], emptyUnders) <- skindCheck [(tgt, Star [])] sty
    ensureEmpty "skindCheck" emptyUnders
    pure (p, v)

-- Kindscheck checks the kinds of the types in a dependent row
kindCheckRow :: Traversable t
             => t (PortName, KindOr (Term Chk Noun)) -- The row to process
             -> Checking (t (PortName, BinderType Brat))
kindCheckRow row = do
  name <- req (Fresh "__kcr")
  {- The state is
      * the ends we've created for kinds in the row,
      * the inputs to the node in the graph IR
      * the outputs of the graph node -}
  (sig, st) <- runStateT (traverse (f name) row) (B0, B0, B0)
  let (_, ins, outs) = st
  req $ AddNode name (BratNode Hypo (ins <>> []) (outs <>> []))
  pure sig
 where
  f :: Name -> (PortName, KindOr (Term Chk Noun))
    -> (StateT
      (Bwd End, Bwd (PortName, Value), Bwd (PortName, Value)) -- state
      Checking (PortName, BinderType Brat)) --underlying monad, result
  f name (p, kOrTy) = do
    (ctx, ins, outs) <- get
    (ctx', kOrTy, ins, outs) <- lift $ case kOrTy of
      Left k -> do
        let dangling = ExEnd $ Ex name (length outs)
        req (Declare dangling k)
        pure (ctx :< dangling, Left k, ins, outs :< (p, kindType k))
      Right ty -> do
        let hungry = NamedPort (In name (length ins)) "type"
        declareTgt hungry (Star [])
        ty <- pure $ changeVar (InxToPar ctx) 0 ty
        ([v], leftovers) <- kindCheck [(hungry, Star [])] ty
        ensureEmpty "kindsCheck leftovers" leftovers
        let v' = (changeVar (ParToInx ctx) 0 v)
        pure (ctx, Right v', ins :< (p, v'), outs)
    put (ctx', ins, outs)
    pure (p, kOrTy)


-- Look for vectors to produce better error messages for mismatched lengths
-- in terms or patterns.
detectVecErrors :: UserName  -- Term constructor name
                -> UserName  -- Type constructor name
                -> [Value]   -- Type arguments
                -> [ValPat]  -- Patterns the type arguments are checked against
                -> Value     -- Type
                -> Either (Term d k) Pattern  -- Term or pattern
                -> Checking (Error -> Error)  -- Returns error wrapper to use for recursion
detectVecErrors vcon (PrefixName [] "Vec") [_, VNum n] [_, VPNum p] ty tp =
  case numMatch B0 n p of
    Left (NumMatchFail _ _) -> do
      p' <- toLenConstr p
      err $ getVecErr tp (show ty) (show n) p'
    -- Even if we succed here, the error might pop up when checking the
    -- rest of the vector. We return a function here that intercepts the
    -- error and extends it to the whole vector.
    _ -> if vcon == PrefixName [] "cons"
         then do fc <- req AskFC
                 pure (consError fc tp (show ty) n)
         else pure id
 where
  -- For constructors that produce something of type Vec we should
  -- only ever get the patterns NP0 (if vcon == PrefixName [] "nil")
  -- and NP1Plus (if vcon == PrefixName [] "cons")
  toLenConstr :: NumPat -> Checking LengthConstraint
  toLenConstr NP0 = pure $ Length 0
  toLenConstr (NP1Plus _) = pure $ LongerThan 0
  toLenConstr p = err $ InternalError ("detectVecErrors: Unexpected pattern: " ++ show p)
detectVecErrors _ _ _ _ _ _ = pure id

getVecErr :: Either (Term d k) Pattern -> (String -> String -> LengthConstraint -> ErrorMsg)
getVecErr (Left tm) = VecLength (show tm)
getVecErr (Right pat) = VecPatLength (show pat)

-- Wrapper extending an error occurring on the RHS of a cons to the whole vector
consError :: FC -> Either (Term d k) Pattern -> String -> NumValue -> Error -> Error
consError fc tp ty exp err = case (tp, msg err) of
    (Left _, VecLength _ _ _ act) -> mkVecError act
    (Right _, VecPatLength _ _ _ act) -> mkVecError act
    _ -> err
 where
  mkVecError act = Err (Just fc) $ getVecErr tp ty (show exp) ((1+) <$> act)


abstractAll' :: (Show (BinderType m), ?my :: Modey m)
            => [(Src, BinderType m)] -> Abstractor
            -> Checking (Env (EnvData m), (Bwd End, Int))
abstractAll' stuff binder = do
  (env, unders, ends) <- abstract (B0, 0) stuff binder
  ensureEmpty "unders after abstract" unders
  pure (env, ends)

abstractAll :: (Show (BinderType m), ?my :: Modey m)
            => [(Src, BinderType m)] -> Abstractor
            -> Checking (Env (EnvData m))
abstractAll stuff binder = fst <$> abstractAll' stuff binder

abstract :: (Show (BinderType m), ?my :: Modey m)
         => (Bwd End, Int)
         -> [(Src, BinderType m)]
         -> Abstractor
         -> Checking (Env (EnvData m) -- Local env for checking body of lambda
                     ,[(Src, BinderType m)] -- rightovers
                     ,(Bwd End, Int)
                     )
abstract ends inputs AEmpty = pure (emptyEnv, inputs, ends)
abstract ends inputs (x :||: y) = do
  (venv, inputs, ends)  <- abstract ends inputs x
  (venv', inputs, ends) <- abstract ends inputs y
  (,inputs, ends) <$> mergeEnvs [venv, venv']
abstract ends inputs (APull ports abst) = do
  inputs <- pullPortsRow ports inputs
  abstract ends inputs abst
abstract (ends, i) ((src, ty):inputs) (APat p) = do
  (env, acc) <- case (?my, ty) of
    (Kerny, ty) -> do
      ty <- evSTy $ changeVar (InxToPar ends) i ty
      (things, acc) <- abstractPattern ?my (ends, i) (src, ty) p
      pure (things, acc)
    (Braty, Right ty) -> do
      ty <- evTy $ changeVar (InxToPar ends) i ty
      (things, acc) <- abstractPattern ?my (ends, i) (src, Right ty) p
      pure (things, acc)
    (Braty, _) -> abstractPattern ?my (ends, i) (src, ty) p
  pure (env, inputs, acc)
abstract _ [] a = err (NothingToBind (show a))

abstractPattern :: Show (BinderType m)
                => Modey m
                -> (Bwd End, Int)
                -> (Src, BinderType m)
                -> Pattern
                -> Checking (Env (EnvData m) -- Local env for checking body of lambda
                            ,(Bwd End, Int)
                            )
abstractPattern m (ends, i) (src, ty) (Bind x)
  = let ctx = case doesItBind m ty of
                Just _ -> (ends :< ExEnd (end src), i + 1)
                Nothing ->  (ends, i)
    in pure (let ?my = m in singletonEnv x (src, ty), ctx)
abstractPattern Braty (ends, i) (src, Left Nat) (Lit tm)
  = simpleCheck Braty TNat tm $> (emptyEnv, (ends :< ExEnd (end src), i + 1))
abstractPattern Braty ends (_, Right ty) (Lit tm) = simpleCheck Braty ty tm $> (emptyEnv, ends)
abstractPattern Kerny ends (_, ty) (Lit tm) = simpleCheck Kerny ty tm $> (emptyEnv, ends)
abstractPattern Braty (ends, i) (dangling, Right ty@(VCon tycon tyargs)) pat@(PCon pcon abst) = do
  (vps,unders) <- clup pcon tycon
  -- Look for vectors to produce better error messages for mismatched lengths
  wrap <- detectVecErrors pcon tycon tyargs vps ty (Right pat)
  zv <- throwLeft $ valMatches tyargs vps
  -- let (ins, outs) = csig vps unders tycon
  (_, [(hungry,_)], overs, _) <- next (show pcon) (Selector pcon) (zv, B0)
                                 [("value", Right ty)] unders
  wire (dangling, ty, hungry)
  (env, abstractUnders, _) <- let ?my = Braty in wrapError wrap $ abstract (ends, i) overs abst
  ensureEmpty "unders after abstract" abstractUnders
  pure (env, (ends, i))
abstractPattern Kerny (ends, i) (dangling, sty) (PCon (PrefixName [] c) abs) = do
  case conFields Kerny c sty of
    Left msg -> err msg
    Right outputs -> do
      (_, [(hungry,_)], overs, _) <- knext "kcons" (Selector (plain "cons")) (B0, ends)
                                         [("value", sty)] outputs
      kwire (dangling, sty, hungry)
      let ?my = Kerny in (,(ends, i)) <$> abstractAll overs abs
abstractPattern Kerny ends (_, Of _ _) PNil = pure (emptyEnv, ends)
abstractPattern Braty (ends, i) (src@(NamedPort dangling _), Left k) pat
  = abstractKind Braty k pat
 where
  abstractKind :: Modey m -> TypeKind -> Pattern -> Checking (Env (EnvData m), (Bwd End, Int))
  abstractKind Braty _ (Bind x) = let ?my = Braty
                                  in pure (singletonEnv x (src, Left k), (ends :< (ExEnd dangling), i + 1))
  abstractKind _ _ (DontCare) = pure (emptyEnv, (ends, i))
  abstractKind _ k (Lit x) = case (k, x) of
    (Nat, Num n) -> req (Define (ExEnd dangling) (VNum (nConstant n))) $> (emptyEnv, (ends, i))
    (Star _, _) -> err MatchingOnTypes
    _ -> err (PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with kind " ++ show k)
  abstractKind Braty Nat p = abstractPattern Braty (ends :< ExEnd (end src), i + 1) (src, Right TNat) p
{- FIXME - looking up nat constructors for `#` is sorely needed
  abstractKind _ Nat (PCon c arg) = do
    case M.lookup c natConstructors of
      -- Is it okay for this to be B0?
      Just (Just p,_) -> case valMatch (endVal Nat dangling) (VPNum p) of
        Nothing -> undefined
        Just (B0 :< v) -> req (Define dangling v) $> (emptyEnv, (ends, i))
      Just (Nothing,_) -> err (PattErr $ show pat ++ " can't be used as a pattern")
      Nothing -> err (PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with kind " ++ show k)
-}
abstractPattern _ ends _ DontCare = pure (emptyEnv, ends)
abstractPattern _ _ (_, ty) pat
  = err (PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with type " ++ show ty)

run :: VEnv
    -> Namespace
    -> Checking a
    -> Either Error (a, ([TypedHole], Graph))
run ve ns m =
  let ctx = Ctx { venv = ve
                , store = initStore
                -- TODO: fill with default constructors
                , constructors = defaultConstructors
                , typeConstructors = defaultTypeConstructors
                , aliasTable = M.empty
                } in
    (\(a,b,_) -> (a,b)) <$> handler m ctx mempty ns
