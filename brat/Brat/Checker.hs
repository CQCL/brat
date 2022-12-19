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
                    ,checkClauses
                    ,TypedHole(..)
                    ,Wire
                    ,wire
                    ,wrapError
                    ,next, knext
                    ,localFC
                    ,emptyEnv
                    ,checkOutputs
                    ,CheckConstraints
                    ,TensorOutputs(..)
                    ) where

import Control.Monad (unless, foldM)
import Control.Monad.Freer
import Data.Functor (($>))
import Data.List (intercalate, transpose)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as M
import Prelude hiding (filter)

import Brat.Checker.Helpers
import Brat.Checker.Monad
import Brat.Checker.Quantity
import Brat.Checker.Types
import Brat.Error
import Brat.FC
import Brat.Graph
import Brat.Naming
import Brat.Search
import Brat.Syntax.Common hiding (end)
import Brat.Syntax.Core
import Brat.Syntax.Simple
import Brat.UserName

mergeEnvs :: [Env a] -> Checking (Env a)
mergeEnvs = foldM combineDisjointEnvs M.empty

emptyEnv :: Env a
emptyEnv = M.empty

singletonEnv :: (?my :: Modey m) => String -> (Src, ValueType m) -> Env (EnvData m)
singletonEnv x input@(_, ty) = case ?my of
  Braty -> M.singleton (plain x) [input]
  Kerny -> let q = if copyable ty then Tons else One
           in  M.singleton (plain x) (q, input)


-- Allows joining the outputs of two nodes together into a `Combo` node
vtensor :: (?my :: Modey m) => [(Src, ValueType m)] -> [(Src, ValueType m)] -> Checking [(Src, ValueType m)]
vtensor ss [] = pure ss
vtensor [] ts = pure ts
vtensor ss ts = do
  let sig = rowToSig ss <> rowToSig ts
  (_, unders, overs) <- anext "tensor" (Combo Row) sig sig
  mapM (\((dangling,ty), (hungry,_)) -> awire (dangling,ty,hungry))
       (zip (ss ++ ts) unders)
  pure $ overs

class TensorOutputs d where
  tensor :: d -> d -> Checking d

instance TensorOutputs () where
  tensor () () = pure ()

instance TensorOutputs [(Src, VType)] where
 tensor = let ?my = Braty in vtensor

instance TensorOutputs [(Src, SType)] where
 tensor = let ?my = Kerny in vtensor

class CombineInputs d where
  combine :: d -> d -> d

instance CombineInputs () where
  combine () () = ()

instance CombineInputs [(Tgt, a)] where
  combine = (++)

type CheckConstraints m k =
  (Eq (ValueType m)
  ,Show (ValueType m)
  ,TensorOutputs (Outputs m Syn)
  ,TensorOutputs (Outputs m Chk)
  ,CombineInputs (Inputs m k)
  ,CombineInputs (Inputs m Noun)
  ,CombineInputs (Inputs m UVerb)
  ,CombineInputs (Inputs m KVerb)
  )

checkInputs :: (CheckConstraints m KVerb, ?my :: Modey m)
            => WC (Term d KVerb)
            -> [(Src, ValueType m)]
            -> [(Tgt, ValueType m)]
            -> Checking [(Src, ValueType m)]
checkInputs _ overs [] = pure overs
checkInputs tm@(WC fc _) (o:overs) (u:unders) = localFC fc $ checkWire o u >>= \case
  Just () -> checkInputs tm overs unders
  Nothing -> err $ TypeMismatch (show tm) (showRow (u :| unders)) (showRow (o :| overs))
checkInputs tm [] unders = typeErr $ "No overs but unders: " ++ show unders ++ " for " ++ show tm

checkOutputs :: (CheckConstraints m k, ?my :: Modey m)
             => WC (Term Syn k)
             -> [(Tgt, ValueType m)]
             -> [(Src, ValueType m)]
             -> Checking [(Tgt, ValueType m)]
checkOutputs _ unders [] = pure unders
checkOutputs tm@(WC fc _) (u:unders) (o:overs) = localFC fc $ checkWire o u >>= \case
  Just () -> checkOutputs tm unders overs
  Nothing -> err $ TypeMismatch (show tm) (showRow (u :| unders)) (showRow (o :| overs))
checkOutputs tm [] overs = typeErr $ "No unders but overs: " ++ show overs ++ " for " ++ show tm

checkClauses :: (?my :: Modey m, CheckConstraints m UVerb)
             => Clause Term UVerb
             -> ChkConnectors m Chk UVerb
             -> Checking (Outputs m Chk
                         ,ChkConnectors m Chk UVerb)
checkClauses Undefined _ = err (InternalError "Checking undefined clause")
checkClauses (NoLhs verb) conn = (\((outs, ()), conns) -> (outs, conns)) <$> check verb conn
checkClauses (Clauses cs) conn = do
  (res@((outs, ()), conns) :| results) <- mapM (\c@(lhs, rhs) ->
    check (WC (clauseFC c) (lhs :\: rhs)) conn) cs
  unless (all (== res) results)
    (fail "Clauses had different rightovers")
  pure (outs, conns)
 where
  clauseFC (lhs, rhs) = FC (start $ fcOf lhs) (end $ fcOf rhs)

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
  -- in Checking mode, each LHS/RHS removes the wires/types it produces from the Unders remaining,
  -- including components of thunks joined together by (Combo Thunk)s in checkOutputs
  ((ins, outs), tys)  <- check s tys
  ((ins', outs'), tys) <- check t tys
  -- in Synthesizing mode, instead we join together the outputs here
  -- with a (Combo Row), although the latter node may not be useful
  outs <- tensor outs outs'
  pure ((combine ins ins', outs), tys)
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
  unders <- pullPorts ports unders
  check t (overs, unders)
check' (t ::: outs) (overs, ()) | Braty <- ?my = do
  (unders, dangling) <- mkIds outs
  ((), overs) <- noUnders $ check t (overs, unders)
  pure (((), dangling), (overs, ()))
 where
  mkIds :: [Output] -> Checking ([(Tgt, VType)] -- Hungry wires
                                ,[(Src, VType)]) -- Dangling wires
  mkIds [] = pure ([], [])
  mkIds ((port, ty):outs) = do
    (_, [under], [over]) <- next "id" Id [(port, ty)] [(port, ty)]
    (unders, overs) <- mkIds outs
    pure (under:unders, over:overs)
check' (Emb t) (overs, unders) = do
  ((ins, outs), (overs, ())) <- check t (overs, ())
  unders <- checkOutputs t unders outs
  pure ((ins, ()), (overs, unders))
check' (Th t) ((), u@(hungry, ty):unders) = case ?my of
  Braty -> do
    case ty of
      C (ss :-> ts) -> checkThunk Braty ss ts ty
      K (R ss) (R ts) -> checkThunk Kerny ss ts ty
      _ -> err $ ExpectedThunk (showMode Braty) (showRow (u :| []))
    pure (((), ()), ((), unders))
  Kerny -> typeErr "no higher order signals! (Th)"
 where
  checkThunk :: CheckConstraints m Noun
             => Modey m
             -> [(PortName, ValueType m)] -> [(PortName, ValueType m)]
             -> ValueType Brat
             -> Checking ()
  checkThunk my ss ts thunkTy = let ?my = my in do
    (src, [], thOvers) <- anext "" Source [] ss
    (tgt, thUnders, []) <- anext "" Target ts []
    (((), ()), (emptyOvers, emptyUnders)) <- check t (thOvers, thUnders)
    ensureEmpty "thunk leftovers" emptyOvers
    ensureEmpty "thunk leftunders" emptyUnders
    (_, _, [(dangling,_)]) <- next "thunk_box" (src :>>: tgt) [] [("fun", thunkTy)]
    wire (dangling, thunkTy, hungry)
check' (Force th) ((), ()) = do
  (((), outs), ((), ())) <- let ?my = Braty in check th ((), ())
  -- pull a bunch of thunks (only!) out of here
  (_, thInputs, thOutputs) <- getThunks ?my outs
  -- Force has no overs, as the result is a KVerb
  pure ((thInputs, thOutputs), ((), ()))
check' (Forget kv) (overs, unders) = do
  ((ins, outs), ((), rightUnders)) <- check kv ((), unders)
  leftOvers <- checkInputs kv overs ins
  pure (((), outs), (leftOvers, rightUnders))
check' (Var x) ((), ()) = case ?my of
  Braty -> vlup x >>= \x -> pure (((), x), ((), ()))
  Kerny -> req (KLup x) >>= \case
    Just output -> pure (((), [output]), ((), ()))
    Nothing -> err $ KVarNotFound (show x)
check' (fun :$: arg) ((), ()) = do
  ((ins, outputs), ((), ())) <- check fun ((), ())
  ((), ()) <- noUnders $ check arg ((), ins)
  pure (((), outputs), ((), ()))
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
    getSuggestions fc = do
      matches <- findMatchingNouns
      let sugg = transpose [ [ tm | tm <- vsearch fc ty ]
                          | (_, ty) <- unders]
      let ms = intercalate ", " . fmap show <$> matches
      let ss = intercalate ", " . fmap show <$> sugg
      pure $ take 5 (ms ++ ss)

    findMatchingNouns :: Checking [[UserName]]
    findMatchingNouns = do
      let tys = snd <$> unders
      env <- req AskVEnv
      let matches = transpose $
            [ [ (nm, src) | (src, _) <- stuff ]
            | (nm, stuff) <- M.assocs env
            , and (zipWith (==) tys (snd <$> stuff))
            ]
      pure $ fmap fst <$> matches

check' (VHole name) (overs, unders) = do
  fc <- req AskFC
  req $ LogHole $ case ?my of
    Braty -> VBHole name fc (overs, unders)
    Kerny -> VKHole name fc (overs, unders)
  pure (((), ()), ([], []))
check'
  (Con (PrefixName [] "cons") (WC _ (x :|: (WC _ (Con (PrefixName [] "cons") (WC _ (y :|: (WC _ (Con (PrefixName [] "nil") (WC _ Empty))))))))))
  ((), (hungry, ty):unders) | (Braty, Product a b) <- (?my, ty) = do
  (_, [first,second], [(dangling,_)]) <- anext "DPair" (Constructor DPair)
                                             [("first", a), ("second", b)]
                                             [("value", Product a b)]
  noUnders $ check x ((), [first])
  noUnders $ check y ((), [second])
  awire (dangling, Product a b, hungry)
  pure (((), ()), ((), unders))
check' pat@(Con (PrefixName [] con) arg) ((), ((hungry, ty):unders))
  | Just (_, n) <- getVec ?my ty = do
      (_, lenUnders, []) <- next "vec_len" Hypo [("value", SimpleTy Natural)] []
      noUnders $ let ?my = Braty in check' n ((), lenUnders)
      n <- evalNat n
      case patternToData ?my con ty of
        Nothing -> error "uhh"
        Just node -> case conFields ?my node ty of
          Nothing -> err $ VecLength n (show ty) (case con of
            "nil" -> Length 0
            "cons" -> LongerThan 0) (show pat)
          Just ins -> do
            outerFC <- req AskFC
            (_, cUnders, [(dangling,_)]) <- anext "" (Constructor node) ins [("value", ty)]
            noUnders $ wrapError (consError n (show ty) pat outerFC) $ check arg ((), cUnders)
            awire (dangling, ty, hungry)
            pure (((), ()), ((), unders))
  | Just node <- patternToData ?my con ty, Just cins <- conFields ?my node ty = do
      (_, cUnders, [(dangling,_)]) <- anext (show con) (Constructor node)
                                          cins [("value", ty)]
      noUnders $ check arg ((), cUnders)
      awire (dangling, ty, hungry)
      pure (((), ()), ((), unders))
  | Just node <- patternToData ?my con ty, Nothing <- conFields ?my node ty
  = typeErr $ show pat ++ " not of type " ++ showRow ((hungry, ty):|unders)

check' t c = case (?my, t, c) of -- remaining cases need to split on ?my
  (Kerny, Simple (Bool _), ((), ((_, Bit):unders))) -> pure (((), ()), ((), unders))
  (Braty, Simple tm, ((), (hungry, SimpleTy ty):unders)) -> do
    simpleCheck ty tm
    (_, [], [(dangling,_)]) <- next (show tm) (Const tm) [] [("value", SimpleTy ty)]
    wire (dangling, SimpleTy ty, hungry)
    pure (((), ()), ((), unders))
  _ -> error $ "check this: " ++ show t

consError :: Int -> String -> Term Chk Noun -> FC -> Error -> Error
consError i ty p fc e = case e of
  Err{msg=VecLength _ _ l _} -> e { msg = VecLength i ty ((1+) <$> l) (show p), fc = Just fc }
  _ -> e

abstractAll :: (Show (ValueType m), ?my :: Modey m)
            => [(Src, ValueType m)] -> Abstractor
            -> Checking (Env (EnvData m))
abstractAll stuff binder = do
  (env, unders) <- abstract stuff binder
  ensureEmpty "unders after abstract" unders
  pure env

abstract :: (Show (ValueType m), ?my :: Modey m)
         => [(Src, ValueType m)]
         -> Abstractor
         -> Checking (Env (EnvData m) -- Local env for checking body of lambda
                     ,[(Src, ValueType m)] -- rightovers
                     )
abstract inputs AEmpty = pure (emptyEnv, inputs)
abstract [] abs = err $ NothingToBind (show abs)
abstract inputs (x :||: y) = do
  (venv, inputs)  <- abstract inputs x
  (venv', inputs) <- abstract inputs y
  (,inputs) <$> mergeEnvs [venv, venv']
abstract inputs (APull ports abst) = do
  inputs <- pullPorts ports inputs
  abstract inputs abst
abstract (input:inputs) (APat (Bind x)) = pure (singletonEnv x input, inputs)
abstract ((dangling,ty):inputs) (APat abs) | Just (ety, n) <- getVec ?my ty =
  (evalNat n) >>= \n -> (,inputs) <$> case abs of
    PNil -> if n == 0
      then pure emptyEnv
      else err $ VecPatLength (show abs) (show ty)
    PCons x xs -> do
      -- A `cons` pattern on the LHS needs to have exactly two binders
      let tailTy = makeVec ety (Simple (Num (n - 1)))
      (_, [(hungry,_)], [head,tail]) <- anext "PCons (Vec)" (Selector DCons)
                                            [("value", ty)] [("head", ety), ("tail", tailTy)]
      awire (dangling, ty, hungry)
      venv <- abstractAll [head] (APat x)
      venv' <- wrapError (consPatErr abs (show ty)) $
                abstractAll [tail] (APat xs)
      mergeEnvs [venv,venv']
    _ -> err $ NotVecPat (show abs) (show ty)
  where
    consPatErr :: Pattern -> String -> Error -> Error
    consPatErr p ty e@Err{msg=(VecPatLength _ _)}
      = e { msg = VecPatLength (prettyPat p) ty }
    consPatErr _ _ e = e

    prettyPat :: Pattern -> String
    prettyPat p = case patList p of
      Just xs -> show xs
      Nothing -> show p

    patList :: Pattern -> Maybe [Pattern]
    patList PNil = Just []
    patList (PCons x xs) = (x:) <$> patList xs
    patList _ = Nothing

abstract ((dangling,ty):inputs) (APat (PCons x (PCons y PNil)))
  | (Braty, Product a b) <- (?my, ty) = do
  (_, [(hungry, _)], overs) <- anext (show DPair) (Selector DPair)
                                    [("value", Product a b)] [("first", a), ("second", b)]
  awire (dangling, Product a b, hungry)
  env <- abstractAll overs (APat x :||: APat y)
  pure (env, inputs)

abstract ((dangling,ty):inputs) (APat (PCon con abs))
  | Just sel <- patternToData ?my con ty
  , Just outs <- conFields ?my sel ty = do
      (_,[(hungry,_)],overs) <- anext (show sel) (Selector sel) [("value", ty)] outs
      awire (dangling, ty, hungry)
      (,inputs) <$> abstractAll overs abs
abstract ((_, ty):inputs) (APat (Lit tm)) = do
  litTy <- case (?my,ty) of
    (Kerny, Bit) -> pure $ Boolean
    (Braty, SimpleTy ty) -> pure $ ty
    (m,_) -> typeErr $ "Can't match literal " ++ show tm ++ (showMode m)
  simpleCheck litTy tm $> (emptyEnv, inputs)
abstract (_:inputs) (APat DontCare) = pure (emptyEnv, inputs)
abstract ((_,ty):_) pat = err (PattErr $
    "Couldn't resolve pattern " ++ show pat ++ " with type " ++ show ty)

run :: (VEnv, [Decl], FC)
    -> Namespace
    -> Checking a
    -> Either Error (a, ([TypedHole], Graph))
run (ve, ds, fc) ns m = let ctx = Ctx { venv = ve
                                   , decls = ds
                                   , typeFC = fc
                                   } in (\(h,g,_) -> (h,g)) <$> handler m ctx ns
