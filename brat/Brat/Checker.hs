{-# LANGUAGE
ConstraintKinds,
FlexibleContexts,
MultiParamTypeClasses,
RankNTypes,
ScopedTypeVariables,
TypeApplications
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
                    ,kindCheck, kindCheckRow, kindCheckAnnotation
                    ) where

import Control.Monad (foldM)
import Control.Monad.Freer
import Data.Bifunctor (second)
import Data.Functor (($>))
-- import Data.List (filter, intercalate, transpose)
import qualified Data.Map as M
import Data.Traversable (for)
import Data.Type.Equality ((:~:)(..))
import Prelude hiding (filter)

import Brat.Checker.Helpers
import Brat.Checker.Monad
import Brat.Checker.Quantity
import Brat.Checker.Types
import Brat.Constructors
import Brat.Error
import Brat.Eval
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
import Hasochism

mergeEnvs :: [Env a] -> Checking (Env a)
mergeEnvs = foldM combineDisjointEnvs M.empty

emptyEnv :: Env a
emptyEnv = M.empty

singletonEnv :: (?my :: Modey m) => String -> (Src, BinderType m) -> Env (EnvData m)
singletonEnv x input@(p, ty) = case ?my of
  Braty -> M.singleton (plain x) [(p, ty)]
  Kerny -> let q = if copyable ty then Tons else One
           in  M.singleton (plain x) (q, input)
   where
    copyable :: SVal Z -> Bool
    copyable VBit = True
    copyable VQ = False
    copyable (VOf elem _) = copyable elem
    copyable (VRho (RPr (_, ty) ro)) = copyable ty && copyable (VRho ro)
    copyable (VRho R0) = True
    --copyable (VRho (REx _ _)) -- fail: this should never happen


class TensorOutputs d where
  tensor :: d -> d -> d

instance TensorOutputs () where
  tensor () () = ()

instance TensorOutputs [(Src, KindOr a)] where
 tensor ss ts = ss <> ts

instance TensorOutputs [(Src, SVal Z)] where
 tensor ss ts = ss <> ts

class CombineInputs d where
  combine :: d -> d -> d

instance CombineInputs () where
  combine () () = ()

instance CombineInputs [(Tgt, a)] where
  combine = (++)

type CheckConstraints m k =
  (Show (ValueType m Z)
  ,Show (BinderType m)
  ,DeBruijn (ValueType m)
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

checkThunk :: (CheckConstraints m UVerb, EvMode m)
           => Modey m
           -> String
           -> CTy m Z
           -> WC (Term Chk UVerb)
           -> Checking Src
checkThunk m name cty tm = do
  ((dangling, _), ()) <- let ?my = m in makeBox name cty $
    \(thOvers, thUnders) -> do
      (((), ()), (emptyOvers, emptyUnders)) <- check tm (thOvers, thUnders)
      ensureEmpty "thunk leftovers" emptyOvers
      ensureEmpty "thunk leftunders" emptyUnders
  pure dangling

check :: (CheckConstraints m k
         ,EvMode m
         ,TensorOutputs (Outputs m d)
         ,?my :: Modey m)
      => WC (Term d k)
      -> ChkConnectors m d k
      -> Checking (SynConnectors m d k
                  ,ChkConnectors m d k)
check (WC fc tm) conn = localFC fc (check' tm conn)

check' :: forall m d k
        . (CheckConstraints m k
          ,EvMode m
          ,TensorOutputs (Outputs m d)
          ,?my :: Modey m)
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
  (ext, overs) <- abstract overs (unWC binder)
  (sycs, ((), unders)) <- localEnv ext $ check body ((), unders)
  pure (sycs, (overs, unders))
check' (Pull ports t) (overs, unders) = do
  unders <- pullPortsRow ports unders
  check t (overs, unders)
check' (t ::: outs) (overs, ()) | Braty <- ?my = do
  (ins :->> outs) :: CTy Brat Z <- kindCheckAnnotation ":::" outs
  (_, hungries, danglies, _) <- next "id" Id (S0,Some (Zy :* S0)) ins outs
  ((), leftOvers) <- noUnders $ check t (overs, hungries)
  pure (((), danglies), (leftOvers, ()))
check' (Emb t) (overs, unders) = do
  ((ins, outs), (overs, ())) <- check t (overs, ())
  unders <- checkOutputs t unders outs
  pure ((ins, ()), (overs, unders))
check' (Th tm) ((), u@(hungry, ty):unders) = case (?my, ty) of
  (Braty, ty) -> do
    ty <- evalBinder Braty ty
    case ty of
      -- the case split here is so we can be sure we have the necessary CheckConstraints
      Right ty@(VFun Braty cty) -> checkThunk Braty "thunk" cty tm >>= wire . (,ty, hungry)
      Right ty@(VFun Kerny cty) -> checkThunk Kerny "thunk" cty tm >>= wire . (,ty, hungry)
      Left (Star args) -> kindCheck [(hungry, Star args)] (Th tm) $> ()
      _ -> err . ExpectedThunk "" $ showRow (u:unders)
    pure (((), ()), ((), unders))
  (Kerny, _) -> err . ThunkInKernel $ show (Th tm)
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
  createThunk :: (CheckConstraints m2 Noun, ?my :: Modey m2, EvMode m2)
              => SynConnectors m2 Syn KVerb
              -> Checking (SynConnectors Brat Syn Noun
                          ,ChkConnectors Brat Syn Noun)
  createThunk (ins, outs) = do
    Some (b :* Flip inR) <- pure $ mkArgRo ?my Zy (rowToSig ins)
    Some (_ :* Flip outR) <- pure $ mkArgRo ?my b (rowToSig outs)
    (thunkOut, ()) <- makeBox "thunk" (inR :->> outR) $
        \(thOvers, thUnders) -> do
          -- if these ensureEmpty's fail then its a bug!
          checkInputs t thOvers ins >>= ensureEmpty "TypedTh inputs"
          checkOutputs t thUnders outs >>= ensureEmpty "TypedTh outputs"
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
check' (Arith op l r) ((), u@(hungry, ty):unders) = case (?my, ty) of
  (Braty, ty) -> do
    ty <- evalBinder Braty ty
    case ty of
      Right TNat -> check_arith TNat
      Right TInt -> check_arith TInt
      Right TFloat -> check_arith TFloat
      _ -> err . ArithNotExpected $ show u
    pure (((), ()), ((), unders))
  (Kerny, _) -> err ArithInKernel
 where
  check_arith ty = let ?my = Braty in do
    let inRo = RPr ("left", ty) $ RPr ("right", ty) R0
    let outRo = RPr ("out", ty) R0
    (_, [lunders, runders], [(dangling, _)], _) <- next (show op) (ArithNode op) (S0, Some $ Zy :* S0) inRo outRo
    (((), ()), ((), leftUnders)) <- check l ((), [lunders])
    ensureEmpty "arith unders" leftUnders
    (((), ()), ((), leftUnders)) <- check r ((), [runders])
    ensureEmpty "arith unders" leftUnders
    wire (dangling, ty, hungry)
    pure (((), ()), ((), unders))
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
check' tm@(Con vcon vargs) ((), ((hungry, ty):unders)) = case (?my, ty) of
  (Braty, Left k) -> do
    (_, leftOvers) <- kindCheck [(hungry, k)] (Con vcon vargs)
    ensureEmpty "kindCheck leftovers" leftOvers
    pure (((), ()), ((), unders))
  (Braty, Right ty) -> do
    VCon tycon tyargs <- eval S0 ty
    (CArgs pats nFree _ argTypeRo) <- clup vcon tycon
    -- Look for vectors to produce better error messages for mismatched lengths
    wrap <- detectVecErrors vcon tycon tyargs pats ty (Left tm)
    Some (ny :* env) <- throwLeft $ valMatches tyargs pats
    -- Make sure env is the correct length for args
    Refl <- throwLeft $ natEqOrBust ny nFree
    let topy = roTop ny argTypeRo
    -- Weaken the scope of ty from Z to the top end of argTypeRo
    let ty' = weaken topy ty
    (_, argUnders, [(dangling, _)], _) <- next (show vcon) (Constructor vcon)
                                          (env, Some (Zy :* S0))
                                          argTypeRo (RPr ("value", ty') R0)
    (((), ()), ((), leftUnders)) <- wrapError wrap $ check vargs ((), argUnders)
    ensureEmpty "con unders" leftUnders
    wire (dangling, ty, hungry)
    pure (((), ()), ((), unders))
  (Kerny, _) -> do
    ty <- eval S0 ty
    outerFC <- req AskFC
    case (ty, vcon, unWC vargs) of
      (VOf ty n, PrefixName [] "nil", Empty) -> case numMatch B0 n NP0 of
        Right B0 -> do
          (_, _, [(dangling, _)], _) <- knext (show vcon) (Constructor vcon) (S0, Some (Zy :* S0))
                                        R0 (RPr ("value", VOf ty (numVal $ VNum n)) R0)
          kwire (dangling, VOf ty (numVal $ VNum n), hungry)
          pure (((), ()), ((), unders))
        _ -> err $ VecLength (show tm) (show $ VOf ty (numVal $ VNum n)) (show n) (Length 0)
      (VOf elemTy succN, PrefixName [] "cons", _) ->
        case numMatch B0 succN (NP1Plus NPVar) of
          Right (B0 :< (VNum n)) -> do
            let tailTy = VOf elemTy (numVal $ VNum n)
            (_, argUnders, [(dangling, _)], _) <-
              knext (show vcon) (Constructor vcon) (S0, Some (Zy :* S0))
              (RPr ("head", elemTy) (RPr ("tail", tailTy) R0))
              (RPr ("value", ty) R0)
            (((), ()), ((), [])) <- wrapError (consError outerFC (Left tm) (show ty) succN) $
                                    check vargs ((), argUnders)
            kwire (dangling, ty, hungry)
            pure (((), ()), ((), unders))
          _ -> err $ VecLength (show tm) (show ty) (show succN) (LongerThan 0)
      (VBit, PrefixName [] c, Empty)
        | c `elem` ["true","false"] -> do
            (_, _, [(dangling, _)], _) <- knext (show vcon) (Constructor vcon) (S0, Some (Zy :* S0)) R0 (RPr ("value", VBit) R0)
            kwire (dangling, VBit, hungry)
            pure (((), ()), ((), unders))
      _ -> err $ UnrecognisedConstructor (show vcon) (show (VBit :: SVal Z))


check' (C cty) ((), ((hungry, ty):unders)) = case (?my, ty) of
  (Braty, Left k) -> do
    (_, leftOvers) <- kindCheck [(hungry, k)] (C cty)
    ensureEmpty "kindCheck leftovers" leftOvers
    pure (((), ()), ((), unders))
  _ -> typeErr $ "Ill-kinded function type: " ++ show cty
check' (Simple tm) ((), ((hungry, ty):unders)) = do
  ty <- evalBinder ?my ty
  case (?my, ty, tm) of
    -- The only SimpleType that checks against a kind is a Nat
    (Braty, Left Nat, Num n) -> do
      (_, _, [(dangling, _)], _) <- next "" (Const (Num n)) (S0,Some (Zy :* S0))
                                    R0 (REx ("value", Nat) (S0 ::- R0))
      let val = VNum (nConstant n)
      defineSrc dangling val
      defineTgt hungry val
      wire (dangling, kindType Nat, hungry)
      pure (((), ()), ((), unders))
    -- No defining needed, so everything else can be unified
    _ -> do
      let vty = biType @m ty
      throwLeft $ simpleCheck ?my vty tm
      (_, _, [(dangling, _)], _) <- anext @m "" (Const tm) (S0,Some (Zy :* S0))
                                     R0 (RPr ("value", vty) R0)
      awire @m (dangling, vty, hungry)
      pure (((), ()), ((), unders))
check' tm _ = error $ "check' " ++ show tm

-- Pass in bot (as a Ny) and get back top (in the Some)
mkArgRo :: Modey m -> Ny bot -> [(PortName, BinderType m)] -> Some (Ny :* Flip (Ro' m) bot)
mkArgRo _ b [] = Some (b :* Flip R0)
mkArgRo Braty b ((p, Left k):rest) = case mkArgRo Braty (Sy b) rest of
  Some (n :* Flip ro) -> Some $ n :* (Flip $ REx (p, k) (S0 ::- ro))
mkArgRo Braty b ((p, Right t):rest) = case mkArgRo Braty b rest of
  Some (n :* Flip ro) -> Some $ n :* (Flip $ RPr (p, weaken b t) ro)
mkArgRo Kerny b ((p,t):rest) = case mkArgRo Kerny b rest of
  Some (n :* Flip ro) -> Some $ n :* (Flip $ RPr (p, weaken b t) ro)

mkKindRo :: [(PortName, TypeKind)] -> Some (Flip (Ro' Brat) bot)
mkKindRo [] = Some (Flip R0)
mkKindRo ((p,k):rest) = case mkKindRo rest of
  Some (Flip ro) -> Some $ Flip $ REx (p,k) (S0 ::- ro)

-- Check a type against a row of kinds, and evaluate it
-- define the ends from unders when appropriate
-- N.B. Wires should be declared before they arrive here, we're going to define them here
kindCheck :: [(Tgt, TypeKind)] -- Kinds checking against
          -> Term Chk Noun     -- The type to scrutinise
          -> Checking ([Val Z] -- The values produced by evaluating term arguments
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
  Just args -> case mkKindRo args of
    Some (Flip args) -> do
      (_, argUnders, [(dangling, _)], _) <- next (show c) (Constructor c) (S0, Some (Zy :* S0))
                                              args --[(p, Left k) | (p, k) <- args])
                                              (REx ("value", Star []) (S0 ::- R0))
      let kindArgs = [ (tgt, k) | (tgt, Left k) <- argUnders ]
      -- recurse first so we Define the necessary argUnders
      (_, emptyUnders) <- kindCheck kindArgs (unWC arg)
      ensureEmpty "kindCheck unders" emptyUnders
      -- now evVa can pick up the definitions
      value <- eval S0 $ VCon c [ endVal k (InEnd (end tgt)) | (tgt, k) <- kindArgs ]
      defineTgt hungry value
      defineSrc dangling value
      wire (dangling, kindType k, hungry)
      pure ([value],unders)
  -- ... or a type alias
  Nothing -> req (ALup c) >>= \case
    Just (aliasArgs, aliasLam) -> case mkKindRo aliasArgs of
      Some (Flip aliasArgs) -> do
        -- It only looks weird that we don't use this `va`
        -- va = endVal of (end kindOut), so not as useful as
        -- the thing we *do* define kindOut as

        (_, argUnders, [(kindOut,_)], ((_ :<< _va), _)) <-
          next "" Hypo (S0, Some (Zy :* S0)) aliasArgs (REx ("type",Star []) (S0 ::- R0))
        -- arg is a juxtaposition
        (args, emptyUnders) <- kindCheck (second (\(Left k) -> k) <$> argUnders) (unWC arg)
        ensureEmpty "alias args" emptyUnders
        val <- apply aliasLam (B0 <>< args)
        defineSrc kindOut val
        defineTgt hungry val
        wire (kindOut, kindType k, hungry)
        pure ([val], unders)
    Nothing -> typeErr $ "Can't find type constructor or type alias " ++ show c
kindCheck ((hungry, Star []):unders) (C (ss :-> ts)) = do
  name <- req (Fresh "__kcc")
  kindCheckRow' (Zy :* S0) M.empty (name,0) ss >>= \case
    (i, env, Some (ez :* Flip inRo)) -> kindCheckRow' ez env (name, i) ts >>= \case
      (_, _, Some (_ :* Flip outRo)) -> do
        let val = VFun Braty (inRo :->> outRo)
        defineTgt hungry val
        pure ([val], unders)
kindCheck ((hungry, Star []):unders) (K (R ss) (R ts)) = do
  -- N.B. Kernels can't bind so we don't need to pass around a stack of ends
  ss <- skindCheckRow ss
  ts <- skindCheckRow ts
  let val = VFun Kerny (foldr RPr R0 ss :->> foldr RPr R0 ts)
  defineTgt hungry val
  pure ([val], unders)

-- N.B. This code is currently only called for checking the validity of type aliases
--
-- Check a lambda as the body of a higher-order kind
-- Body will contain Core.Var for things that correspond to variables bound by xs
kindCheck ((hungry, Star args):unders) (Th (WC _ (xs :\: (WC fc body)))) = case mkKindRo args of
  Some (Flip ro) -> do
    -- Make some ends (outputs here) to correspond to hypothetical arguments to the alias
    (_, [], kovers, (_, endz)) <- next "aliargs" Hypo (S0, Some (Zy :* S0)) R0 ro
    ext <- let ?my = Braty in abstractAll kovers (unWC xs)
    -- kindCheck the alias with those arguments into a second Hypo node
    (_, [(p, Left k)], _, _) <- next "alias" Hypo (S0, Some (Zy :* S0))
                                   (REx ("type", Star []) (S0 ::- R0)) R0
    ([vbody], emptyUnders) <- localFC fc $ localVEnv ext $ kindCheck [(p, k)] body
    ensureEmpty "kindCheck unders" emptyUnders
    vbody <- eval S0 vbody
    let vlam = case endz of
          Some (ny :* endz) -> lambdify endz (changeVar (ParToInx (AddZ ny) endz) vbody)
    defineTgt hungry vlam
    pure ([vlam], unders)
 where
  lambdify :: Stack Z End i -> Val i -> Val Z
  lambdify S0 v = v
  lambdify (zx :<< _) v = lambdify zx (VLam (S0 ::- v))
kindCheck unders (Emb (WC _ (Var v))) = vlup v >>= f unders
 where
  f :: [(Tgt, TypeKind)]
    -> [(Src, BinderType Brat)]
    -> Checking ([Val Z], [(Tgt, TypeKind)])
  f unders [] = pure ([], unders)
  f [] _ = typeErr "Empty unders"
  f  ((hungry, k'):us) ((dangling, Left k):xs) = do
    throwLeft $ kindEq k k'
    wire (dangling, kindType k, hungry)
    value <- eval S0 (endVal k (ExEnd (end dangling)))
    defineTgt hungry value
    (vs, leftUnders) <- f us xs
    pure (value:vs, leftUnders)
  f _ (x:_) = err $ InternalError $ "Kindchecking a row which contains " ++ show x
-- TODO: Add other operations on numbers
kindCheck ((hungry, Nat):unders) (Simple (Num n)) | n >= 0 = do
  (_, _, [(dangling, _)], _) <- next "" (Const (Num n)) (S0,Some (Zy :* S0)) R0 (REx ("value", Nat) (S0 ::- R0))
  let value = VNum (nConstant n)
  defineTgt hungry value
  defineSrc dangling value
  wire (dangling, TNat, hungry)
  pure ([value], unders)
kindCheck ((hungry, Nat):unders) (Con c arg)
 | Just (_, f) <- M.lookup c natConstructors = do
     -- All nat constructors have one input and one output
     (_, [(chungry,_)], [(cdangling,_)], _) <- next (show c) (Constructor c) (S0, Some (Zy :* S0))
                                               (REx ("in", Nat) (S0 ::- R0))
                                               (REx ("out", Nat) (S0 ::- R0))
     wire (cdangling, TNat, hungry)
     ([VNum nv], us) <- kindCheck [(chungry, Nat)] (unWC arg)
     ensureEmpty "kindCheck unders" us
     v <- eval S0 (VNum (f nv))
     defineSrc cdangling v
     defineTgt hungry v
     pure ([v], unders)
kindCheck unders tm = err $ Unimplemented "kindCheck" [showRow unders, show tm]

-- kindCheck, but for kernel types
-- Note that all dependency happens in classical terms,
-- so we only really care about the index in `Of`
skindCheck :: [(Tgt, TypeKind)]
           -> SType' (Term Chk Noun)
           -> Checking ([SVal Z], [(Tgt, TypeKind)])
skindCheck ((_, Star []):unders) (Q _) = pure ([VQ], unders)
skindCheck ((_, Star []):unders) Bit = pure ([VBit], unders)
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
  pure ([VOf vsty (numVal vn)], unders)
skindCheck ((_, Star []):unders) (Rho (R row))
  = (,unders) . (:[]) . VRho . foldr RPr R0 <$> skindCheckRow row
skindCheck _ _ = err $ InternalError "Kind checking in a kernel"

skindCheckRow :: [(PortName, SType' (Term Chk Noun))] -> Checking [(PortName, SVal Z)]
skindCheckRow xs = do
  node <- req (Fresh "")
  for (zip xs [0..]) $ \((p, sty), i) -> do
    let tgt = NamedPort (In node i) p
    declareTgt tgt (Star [])
    ([v], emptyUnders) <- skindCheck [(tgt, Star [])] sty
    ensureEmpty "skindCheck" emptyUnders
    pure (p, v)

-- Checks the kinds of the types in a dependent row
kindCheckRow :: String -- for node name
             -> [(PortName, KindOr (Term Chk Noun))] -- The row to process
             -> Checking (Some (Flip (Ro' Brat) Z))
kindCheckRow name r = do
  name <- req $ Fresh $ "__kcr_" ++ name
  kindCheckRow' (Zy :* S0) M.empty (name, 0) r >>= \case
    (_, _, Some (_ :* flipped_ro)) -> pure $ Some flipped_ro

-- Checks that an annotation is a valid row, returning the
-- evaluation of the type of an Id node passing through such values
kindCheckAnnotation :: String -- for node name
                    -> [(PortName, KindOr (Term Chk Noun))]
                    -> Checking (CTy Brat Z)
kindCheckAnnotation name outs = do
  name <- req (Fresh $ "__kca_" ++ name)
  kindCheckRow' (Zy :* S0) M.empty (name, 0) outs >>= \case
    (_, _, Some ((n :* s) :* Flip ins)) ->
      -- Make a copy of ins whose free indices claim to start where the
      -- first left off. Since any references to the Ends in `s` have
      -- already been converted to (bound) Inx's, this does nothing,
      -- but persuades the Haskell typechecker it's ok to use the copy
      -- as return types (that happen not to mention the argument types).
      case varChangerThroughRo (ParToInx (AddZ n) s) ins of
        Some (_ :* Flip outs) -> pure (ins :->> outs)

kindCheckRow' :: Endz n -- kind outports so far
              -> VEnv -- from string variable names to VPar's
              -> (Name, Int) -- node name and next free input (under to 'kindCheck' a type)
              -> [(PortName, KindOr (Term Chk Noun))]
              -> Checking (Int, VEnv, Some (Endz :* Flip (Ro' Brat) n))
kindCheckRow' ez env (_,i) [] = pure (i, env, Some (ez :* Flip R0))
kindCheckRow' ez@(ny :* s) env (name, i) ((p, Right tm):rest) = do
  let hungry = NamedPort (In name i) p -- or always call it "type"?
  declareTgt hungry (Star [])
  ([v], []) <- localVEnv env $ kindCheck [(hungry, Star [])] tm -- TODO give proper errors on failed match
  -- v has no dangling Inx's but contains Par's in `s`. Convert to `n` Inx's
  v <- pure $ changeVar (ParToInx (AddZ ny) s) v
  (i, env, ser) <- kindCheckRow' ez env (name, i+1) rest
  case ser of
    Some (s_m :* Flip ro) -> pure (i, env, Some (s_m :* Flip (RPr (p, v) ro)))
kindCheckRow' (ny :* s) env (name,i) ((p, Left k):rest) = do -- s is Stack Z n
  let dangling = Ex name (ny2int ny)
  req (Declare (ExEnd dangling) k)
  env <- pure $ M.insert (plain p) [(NamedPort dangling p, Left k)] env
  (i, env, ser) <- kindCheckRow' (Sy ny :* (s :<< ExEnd dangling)) env (name, i) rest
  case ser of
    Some (s_m :* Flip ro) -> -- for some m>=S(n), there is Stack S(n) m, ro is Ro Brat S(n) m
      -- The Some we return quantifies over the same m, but the ::- allows us to
      -- return a Ro starting at n rather than ro starting at S(n)
      pure (i, env, Some (s_m :* Flip (REx (p,k) (S0 ::- ro))))

-- Look for vectors to produce better error messages for mismatched lengths
-- in terms or patterns.
detectVecErrors :: UserName  -- Term constructor name
                -> UserName  -- Type constructor name
                -> [Val Z]   -- Type arguments
                -> [ValPat]  -- Patterns the type arguments are checked against
                -> Val Z     -- Type
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
consError :: FC -> Either (Term d k) Pattern -> String -> NumVal n -> Error -> Error
consError fc tp ty exp err = case (tp, msg err) of
    (Left _, VecLength _ _ _ act) -> mkVecError act
    (Right _, VecPatLength _ _ _ act) -> mkVecError act
    _ -> err
 where
  mkVecError act = Err (Just fc) $ getVecErr tp ty (show exp) ((1+) <$> act)

abstractAll :: (Show (BinderType m), EvMode m, ?my :: Modey m)
            => [(Src, BinderType m)] -> Abstractor
            -> Checking (Env (EnvData m))
abstractAll stuff binder = do
    (env, unders) <- abstract stuff binder
    ensureEmpty "unders after abstract" unders
    pure env

abstract :: forall m
          . (Show (BinderType m), ?my :: Modey m, EvMode m)
         => [(Src, BinderType m)]
         -> Abstractor
         -> Checking (Env (EnvData m) -- Local env for checking body of lambda
                     ,[(Src, BinderType m)] -- rightovers
                     )
abstract inputs AEmpty = pure (emptyEnv, inputs)
abstract inputs (x :||: y) = do
  (venv, inputs)  <- abstract inputs x
  (venv', inputs) <- abstract inputs y
  (,inputs) <$> mergeEnvs [venv, venv']
abstract inputs (APull ports abst) = do
  inputs <- pullPortsRow ports inputs
  abstract inputs abst
abstract ((src, ty):inputs) (APat p) = (,inputs) <$> abstractPattern ?my (src, ty) p
abstract [] a = err (NothingToBind (show a))

abstractPattern :: Show (BinderType m)
                => Modey m
                -> (Src, BinderType m)
                -> Pattern
                -> Checking (Env (EnvData m)) -- Local env for checking body of lambda
abstractPattern m (src, ty) (Bind x) = let ?my = m in pure $ singletonEnv x (src, ty)
abstractPattern Braty (_, Left Nat) (Lit tm) = throwLeft (simpleCheck Braty TNat tm) $> emptyEnv
abstractPattern Braty (_, Right ty) (Lit tm) = throwLeft (simpleCheck Braty ty tm) $> emptyEnv
abstractPattern Kerny (_, ty) (Lit tm) = throwLeft (simpleCheck Kerny ty tm) $> emptyEnv
abstractPattern Braty (dangling, Right ty@(VCon tycon tyargs)) pat@(PCon pcon abst) = do
  (CArgs vps nFree _ unders) <- clup pcon tycon
  -- Look for vectors to produce better error messages for mismatched lengths
  wrap <- detectVecErrors pcon tycon tyargs vps ty (Right pat)
  Some (ny :* zv) <- throwLeft $ valMatches tyargs vps
  Refl <- throwLeft $ natEqOrBust ny nFree
  -- ty is Inx-closed, but `next` expects it to have <ny> free vars,
  -- so persuade the type system of that
  let ty' = weaken ny ty
  (_, [(hungry, _)], overs, _) <- next (show pcon) (Selector pcon) (zv, Some (Zy :* S0)) (RPr ("value", ty') R0) unders
  wire (dangling, ty, hungry)
  (env, abstractUnders) <- let ?my = Braty in wrapError wrap $ abstract overs abst
  ensureEmpty "unders after abstract" abstractUnders
  pure env
abstractPattern Kerny (dangling, sty) (PCon (PrefixName [] c) abs) = do
  outputs <- kConFields c sty
  (_, [(hungry,_)], overs, _) <- knext "kcons" (Selector (plain "cons")) (S0, Some (Zy :* S0))
                                 (RPr ("value", sty) R0) outputs
  kwire (dangling, sty, hungry)
  let ?my = Kerny in abstractAll overs abs
 where
  -- Tells abstractPattern what you get when you take apart a constructor
  kConFields :: String -> SVal Z -> Checking (Ro Kernel Z Z)
  -- Note: These are the only Kerny constructors
  kConFields "nil" (VOf _ n) = do
    n <- eval S0 n
    throwLeft $ numMatch B0 n NP0
    pure R0
  kConFields "cons" (VOf elTy n) = do
    elTy <- eval S0 elTy
    matches <- throwLeft $ numMatch B0 n (NP1Plus NPVar)
    case matches of
      B0 :< VNum pred -> pure (RPr ("head", elTy) (RPr ("tail", VOf elTy pred) R0))
      _ -> err $ InternalError "conFields: Invalid cons length"
  kConFields con VBit | con `elem` ["true", "false"] = pure R0
  kConFields con ty = err $ TyConNotFound (show ty) con
abstractPattern Kerny (_, VOf _ _) PNil = pure emptyEnv
abstractPattern Braty (dangling, Left k) pat = abstractKind k pat
 where
  abstractKind :: TypeKind -> Pattern -> Checking (Env (EnvData Brat))
  abstractKind _ (Bind x) = let ?my = Braty in pure (singletonEnv x (dangling, Left k))
  abstractKind _ (DontCare) = pure emptyEnv
  abstractKind k (Lit x) = case (k, x) of
    (Nat, Num n) -> defineSrc dangling (VNum (nConstant n)) $> emptyEnv
    (Star _, _) -> err MatchingOnTypes
    _ -> err (PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with kind " ++ show k)
--  abstractKind Braty Nat p = abstractPattern Braty (src, Right TNat) p
  abstractKind Nat pat@(PCon c parg) = do
    case M.lookup c natConstructors of
      Just (Just p, rel) -> case numMatch B0 (nVar (VPar (ExEnd (end dangling)))) p of
        -- TODO: Make some Nat deconstructor node for the wiring here
        Right (B0 :< VNum v) -> do
          (_, [], [(newDangling, _)], _) <- next "Nat pat destructor" Hypo (S0, Some (Zy :* S0)) R0 (REx ("", Nat) (S0 ::- R0))
          defineSrc newDangling (VNum v)
          defineSrc dangling (VNum (rel v))
          let ?my = Braty in abstractAll [(newDangling, Left Nat)] parg
        _ -> err . PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with kind #"
      Just (Nothing,_) -> err (PattErr $ show pat ++ " can't be used as a pattern")
      Nothing -> err (PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with kind " ++ show k)
  abstractKind k (PCon _ _) = err $ PattErr $ "No patterns for matching kind " ++ show k

abstractPattern _ _ DontCare = pure emptyEnv
abstractPattern _ (_, ty) pat
  = err (PattErr $ "Couldn't resolve pattern " ++ show pat ++ " with type " ++ show ty)

weaken :: DeBruijn v => Ny n -> v Z -> v n
-- TODO: here we call changeVar with some fake ends that don't get abstracted.
-- This is not the right way to do this, and we should replace this with proper weakening.
weaken n ty = changeVar (ParToInx (AddZ n) (mkStk n)) ty
 where
  -- TODO: Remove this; perhaps another VarChanger?
  mkStk :: Ny n -> Stack Z End n
  mkStk Zy = S0
  mkStk (Sy n) = (mkStk n) :<< InEnd (In (MkName []) (-1)) -- an end that does not exist

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
