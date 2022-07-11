{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Brat.Checker (check
                    ,run
                    ,VEnv
                    ,Checking
                    ,Connectors
                    ,Graph
                    ,Mode(..)
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
                    ,TensorOutputs(..)
                    ) where

import Control.Monad (unless, when, foldM)
import Control.Monad.Freer
import Data.Functor (($>))
import Data.List (intercalate, transpose)
import Data.List.NonEmpty (NonEmpty(..), last)
import qualified Data.Map as M
import Prelude hiding (filter, last)

import Brat.Checker.Combine (combinationsWithLeftovers)
import Brat.Checker.Helpers
import Brat.Checker.Monad
import Brat.Checker.Quantity
import Brat.Checker.Types
import Brat.Error
import Brat.FC
import Brat.Graph
import Brat.Naming
import Brat.Search
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.UserName

import Debug.Trace

mergeEnvs :: [Env a] -> Checking (Env a)
mergeEnvs = foldM combineDisjointEnvs M.empty

emptyEnv :: Env a
emptyEnv = M.empty

class (AType ty) => EnvFor e ty where
  singletonEnv :: String -> (Src, ty) -> Env e
  abstractPattern :: [(Src, ty)] -> Pattern Abstractor -> Maybe (Checking (Env e, [(Src, ty)]))
  abstractVecLit :: (Src, ty) -> [Abstractor] -> Checking (Env e)

instance EnvFor [(Src, VType)] VType where
  singletonEnv x input = M.singleton (plain x) [input]
  abstractPattern inputs@((_, SimpleTy Natural):_) (POnePlus (Bind x)) = Just $ abstract inputs (Bind x)
  abstractPattern inputs@((_, SimpleTy Natural):_) (PTwoTimes (Bind x)) = Just $ abstract inputs (Bind x)
  abstractPattern ((_, List _):inputs) PNil = Just $ pure (emptyEnv, inputs)
  abstractPattern ((_, List ty):inputs) (PCons (x :||: xs)) = Just $ do
    node <- next "PCons (List)" Hypo [("head", ty), ("tail", List ty)] []
    venv <- abstractAll [((node, "head"), ty)] x
    venv' <- abstractAll [((node, "tail"), List ty)] xs
    (,inputs) <$> combineDisjointEnvs venv venv'
  abstractPattern ((src, Option ty):inputs) (PSome x) = Just $ abstract ((src, ty):inputs) x
  abstractPattern ((_, Option _):inputs) PNone = Just $ pure (emptyEnv, inputs)
  abstractPattern ((_, vty@(Vector ty n)):inputs) abs = Just $ do
    n <- evalNat n
    (,inputs) <$> abstractVecPat (ty, n) vty abs
  abstractPattern _ _ = Nothing

  abstractVecLit (_, Vector ty n) abss = abstractVecLitVec (ty, n) abss

  abstractVecLit (_, List ty) xs = do
    node <- next "List literal pattern" Hypo [("type", ty)] []
    venvs <- mapM (abstractAll [((node, "type"), ty)]) xs
    mergeEnvs venvs

  abstractVecLit (src, Product l r) [a,b] = do
    venv <- abstractAll [(src, l)] a
    venv' <- abstractAll [(src, r)] b
    combineDisjointEnvs venv venv'

  abstractVecLit _ xs = err $ PattErr $ "Can't bind to Vector Literal " ++ (show xs)

instance EnvFor (Quantity, (Src, SType)) SType where
  singletonEnv x input@(_, ty) =
    let q = if copyable ty then Tons else One
    in M.singleton (plain x) (q, input)
  abstractPattern ((_, vty@(Of ty n)):inputs) abs = Just $ do
    n <- evalNat n
    (,inputs) <$> abstractVecPat (ty, n) vty abs

  abstractPattern _ _ = Nothing
  abstractVecLit ((_, Of ty n)) abss = abstractVecLitVec (ty, n) abss
  abstractVecLit _ xs = err $ PattErr $ "Can't bind to Vector Literal " ++ (show xs) ++ " in kernel"

abstractVecPat :: (EnvFor e aType)
               => (aType, Int)
               -> aType -- for error message
               -> Pattern Abstractor
               -> Checking (Env e)
abstractVecPat (ty, n) vty p =
  case p of
    PNil -> do
      if n == 0
        then pure emptyEnv
        else err $ VecLength n (show vty) "0" (show p)
    PCons (x :||: xs) -> do
      -- A `cons` pattern on the LHS needs to have exactly two binders
      let tailTy = makeVec ty (Simple (Num (n - 1)))
      node <- anext "PCons (Vec)" Hypo [("head", ty), ("tail", tailTy)] []
      venv <- abstractAll [((node, "head"), ty)] x
      venv' <- abstractAll [((node, "tail"), tailTy)] xs
      mergeEnvs [venv,venv']
    _ -> err $ NotVecPat (show p) (show (makeVec ty (Simple (Num n))))

abstractVecLitVec :: (EnvFor e aType)
                  => (aType, Term Chk Noun)
                  -> [Abstractor]
                  -> Checking (Env e)
abstractVecLitVec (ty, n) xs = do
    node <- next "natHypo" Hypo [("value", SimpleTy Natural)] []
    check' n ((), [((node, "value"), SimpleTy Natural)])
    n <- evalNat n
    unless (n == length xs)
      (err $ VecPatLength (show xs) (show (makeVec ty (Simple (Num n)))))
    envs <- mapM (abstractAll [((node, "type"), ty)]) xs
    mergeEnvs envs

-- Run a type-checking computation, and ensure that what comes back is a classical thunk
-- TODO: this should be able to work on kernels too
onlyThunk :: Checking (Outputs Brat Syn, Connectors Brat Syn Noun)
          -> Checking (Src, [Input], [Output])
onlyThunk m = do
  (outs, ((), ())) <- m
  outs1 <- case outs of
    [] -> err $ ExpectedThunk "empty row"
    x:xs -> pure (x :| xs)
  rows <- combinationsWithLeftovers outs1
  case last rows of
    ((src, C (ss :-> ts)), []) -> pure (src, ss, ts)
    ((_, C _), (u:us)) -> typeErr $ "Expected empty unders, got: " ++ showRow (u :| us)
    (x, xs) -> err $ ExpectedThunk (showRow (x :| xs))

-- Allows joining the outputs of two nodes together into a `Combo` node
class TensorOutputs d where
  tensor :: d -> d -> Checking d

instance TensorOutputs () where
  tensor () () = pure ()

instance AType ty => TensorOutputs [(Src, ty)] where
  tensor ss [] = pure ss
  tensor [] ts = pure ts
  tensor ss ts = do
    let sig = mergeSigs (rowToSig ss) (rowToSig ts)
    tensorNode <- anext "tensor" (Combo Row) sig sig
    mapM (\((src,ty),dstPort) -> awire (src,ty,(tensorNode,dstPort))) (zip (ss ++ ts) (map fst sig))
    pure $ sigToRow tensorNode sig

data SubtractionResult a = ExactlyEqual | Remainder a

class SubtractThunks a where
  subtractThunks :: a -> a -> Maybe (SubtractionResult a)

instance SubtractThunks VType where
  subtractThunks (C (ss :-> ts)) (C (us :-> vs)) = do
    as <- ss `subtractSig` us
    rs <- ts `subtractSig` vs
    return $ case (as,rs) of
      ([], []) -> ExactlyEqual
      _ -> Remainder $ C (as :-> rs)

  subtractThunks (K (R ss) (R ts)) (K (R us) (R vs)) = do
    args <- ss `subtractSig` us
    res <- ts `subtractSig` vs
    return $ case (args, res) of
      ([], []) -> ExactlyEqual
      _ -> Remainder $ K (R args) (R res)

  subtractThunks a b = if a == b then Just ExactlyEqual else Nothing

instance SubtractThunks SType where
  subtractThunks (Rho (R r)) (Rho (R s)) = do
    t <- r `subtractSig` s
    return (if t == [] then ExactlyEqual else Remainder $ Rho (R t))

  subtractThunks a b = if a == b then Just ExactlyEqual else Nothing

checkOutputs :: (Eq t, SubtractThunks t, AType t)
             => WC (Term Syn k)
             -> [(Tgt, t)]
             -> [(Src, t)]
             -> Checking [(Tgt, t)]
checkOutputs _ tys [] = pure tys
checkOutputs tm ((tgt, ty):tys) ((src, ty'):outs) = case ty `subtractThunks` ty' of
    Just ExactlyEqual -> awire (src, ty, tgt) *> checkOutputs tm tys outs
    Just (Remainder rest) -> do
        -- We'll combine the first src with some other thunk to make the first tys.
        -- This node outputs the combined thunk
        combo <- anext ("funcs_" ++ show src) (Combo Thunk) [("in1", ty'), ("in2", rest)] [("fun", ty)]
        awire ((combo, "fun"), ty, tgt)
        -- Wire in the first input to the combo, but we don't have the second yet
        awire (src, ty', (combo, "in1"))
        -- So leave the second for recursive call or to return as an Under still required
        checkOutputs tm (((combo, "in2"), rest):tys) outs
    Nothing -> let exp = showRow ((tgt, ty) :| tys)
                   act = showRow ((src, ty') :| outs)
               in req $ Throw $
                  Err (Just $ fcOf tm) Nothing $
                  TypeMismatch (show tm) exp act

checkClauses :: Clause Term Verb
             -> Connectors Brat Chk Verb
             -> Checking (Outputs Brat Chk
                         ,Connectors Brat Chk Verb)
checkClauses Undefined _ = err (InternalError "Checking undefined clause")
checkClauses (NoLhs verb) conn = check verb conn
checkClauses (Clauses cs) conn = do
  (res :| results) <- mapM (\c -> checkClause c conn) cs
  unless (all (== res) results)
    (fail "Clauses had different rightovers")
  pure res
 where
  checkClause :: (WC Abstractor, WC (Term Chk Noun))
              -> Connectors Brat Chk Verb
              -> Checking (Outputs Brat Chk
                          ,Connectors Brat Chk Verb)
  checkClause (lhs, rhs) =
   let lfc = fcOf lhs
       rfc = fcOf rhs
   in  check (WC (FC (start lfc) (end rfc)) (lhs :\: rhs))

check :: TensorOutputs (Outputs Brat d)
      => WC (Term d k)
      -> Connectors Brat d k
      -> Checking (Outputs Brat d
                  ,Connectors Brat d k)
check (WC fc tm) conn = localFC fc (check' tm conn)

check' :: TensorOutputs (Outputs Brat d)
       => Term d k
       -> Connectors Brat d k
       -> Checking (Outputs Brat d
                   ,Connectors Brat d k) -- rightovers
check' (s :|: t) tys = do
  -- in Checking mode, each LHS/RHS removes the wires/types it produces from the Unders remaining,
  -- including components of thunks joined together by (Combo Thunk)s in checkOutputs
  (outs, tys)  <- check s tys
  (outs', tys) <- check t tys
  -- in Synthesizing mode, instead we join together the outputs here
  -- with a (Combo Row), although the latter node may not be useful
  outs <- tensor outs outs'
  pure (outs, tys)
check' (s :-: t) (overs, unders) = do
  (overs, (rightovers, ())) <- check s (overs, ())
  (outs,  (emptyOvers, rightunders)) <- check t (overs, unders)
  ensureEmpty "overs" emptyOvers
  pure (outs, (rightovers, rightunders))
check' (binder :\: body) (overs, unders) = do
  (vext, overs) <- abstract overs (unWC binder)
  (outs, ((), unders)) <- localVEnv vext $ check body ((), unders)
  pure (outs, (overs, unders))
check' (Pull ports t) (overs, unders) = do
  unders <- pullPorts ports unders
  check t (overs, unders)
check'  (t ::: outs) (overs, ()) = do
  (unders, dangling) <- mkIds outs
  ((), overs) <- noUnders $ check t (overs, unders)
  pure (dangling, (overs, ()))
 where
  mkIds :: [Output] -> Checking ([(Tgt, VType)] -- Hungry wires
                                ,[(Src, VType)]) -- Dangling wires
  mkIds [] = pure ([], [])
  mkIds ((port, ty):outs) = do
    node <- next "id" Id [(port, ty)] [(port, ty)]
    (hungry, dangling) <- mkIds outs
    pure (((node, port), ty):hungry, ((node, port), ty):dangling)
check' (Emb t) (overs, unders) = do
  (outs, (overs, ())) <- check t (overs, ())
  unders <- checkOutputs t unders outs
  pure ((), (overs, unders))

check' (Th t) (overs, (tgt, ty@(C (ss :-> ts))):unders) = do
  srcNode <- next "thunk_source" Source [] ss
  tgtNode <- next "thunk_target" Target ts []
  let thOvers  = [ ((srcNode, port), ty)| (port, ty) <- ss]
  let thUnders = [ ((tgtNode, port), ty)| (port, ty) <- ts]
  ((), (emptyOvers, emptyUnders)) <- check t (thOvers, thUnders)
  ensureEmpty "overs" emptyOvers
  ensureEmpty "unders" emptyUnders
  funNode <- next "box" (srcNode :>>: tgtNode) [] [("fun", C $ ss :-> ts)]
  wire ((funNode, "fun"), Right ty, tgt)
  pure ((), (overs, unders))
check' (Th t) (overs, (tgt, ty@(K (R ss) (R ts))):unders) = do
  srcNode <- knext "thunk_source" Source [] ss
  tgtNode <- knext "thunk_target" Target ts []
  let thOvers  = [ ((srcNode, port), ty)| (port, ty) <- ss]
  let thUnders = [ ((tgtNode, port), ty)| (port, ty) <- ts]
  ((), (emptyOvers, emptyUnders)) <- kcheck t (thOvers, thUnders)
  ensureEmpty "overs" emptyOvers
  ensureEmpty "unders" emptyUnders
  funNode <- next "box" (srcNode :>>: tgtNode) [] [("fun", K (R ss) (R ts))]
  wire ((funNode, "fun"), Right ty, tgt)
  pure ((), (overs, unders))
check' (Var x) ((), ()) = do
  output <- vlup x
  pure (output, ((), ()))
check' (fun :$: arg) ((), ()) = do
  (src, ss, ts) <- onlyThunk $ check fun ((), ())
  evalNode <- next "eval" (Eval src) ss ts
  ((), ()) <- noUnders $ check arg ((), [((evalNode, port), ty) | (port, ty) <- ss])
  pure ([ ((evalNode, port), ty) | (port, ty) <- ts], ((), ()))
check' (Simple tm) ((), ((src, p), SimpleTy ty):unders) = do
  simpleCheck ty tm
  this <- next (show tm) (Const tm) [] [("value", SimpleTy ty)]
  wire ((this, "value"), Right (SimpleTy ty), (src, p))
  pure ((), ((), unders))
check' (Vec [a,b]) ((), (tgt, Product s t):unders) = do
  mkpair <- next "mkpair" (Constructor CPair) [("first", s), ("second", t)] [("value", Product s t)]
  check1Under ((mkpair, "first"), s) a
  check1Under ((mkpair, "second"), t) b
  wire ((mkpair, "value"), Right (Product s t), tgt)
  pure ((), ((), unders))
check' (Vec elems) ((), (tgt, vty@(Vector ty n)):unders) = do
  hypo <- next "nat hypo" Hypo [("ty", SimpleTy Natural)] []
  fc <- req AskFC
  check1Under ((hypo, "ty"), SimpleTy Natural) (WC fc n)
  len <- evalNat n
  unless (length elems == len)
    (err $ VecLength len (show vty) (show (length elems)) (show elems))
  let inputs = [('e':show i,ty) | i <- [0..(len-1)]]
  mkvec <- next "mkvec" (Constructor CVec) inputs [("value", Vector ty n)]
  sequence_ [noUnders $ check x ((), [((mkvec, p), ty)]) | (x, (p, ty)) <- zip elems inputs]
  wire ((mkvec,"value"), Right (Vector ty n), tgt)
  pure ((), ((), unders))

check' (Vec elems) ((), (tgt, List ty):unders) = do
  let inputs = [('e':show i, ty) | (i,_) <- zip [0..] elems]
  mklist <- next "mklist" (Constructor CList) inputs [("value", List ty)]
  sequence_ [noUnders $ check x ((), [((mklist, p), ty)]) | (x, (p, ty)) <- zip elems inputs]
  wire ((mklist,"value"), Right (List ty), tgt)
  pure ((), ((), unders))

check' (NHole name) ((), unders) = do
  fc <- req AskFC
  suggestions <- getSuggestions fc
  req $ LogHole $ NBHole name fc suggestions ((), unders)
  pure ((), ((), []))
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
  req $ LogHole $ VBHole name fc (overs, unders)
  pure ((), ([], []))
check' (Slice big slice) ((), (_, s :<<<: t):unders) = do
  natHyp <- next "slice check" Hypo [] []
  fc <- req AskFC
  check1Under ((natHyp, "weeEnd"), SimpleTy Natural) (WC fc s)
  check1Under ((natHyp, "bigEnd"), SimpleTy Natural) (WC fc t)
  check1Under ((natHyp, "bigEnd2"), SimpleTy Natural) big
  checkNats ((natHyp, "slice"), SimpleTy Natural) slice
  pred <- bigEndPred slice
  checkSlice pred

  s <- evalNat s
  t <- evalNat t
  big <- evalNat (unWC big)
  wee <- weeEnd slice t
  unless (t == big)
    (fail $ "the big end of " ++ show t ++ " should be " ++ show wee ++ ", not " ++ show big)
  unless (s == wee)
    (fail $ "the wee end of " ++ show slice ++ " should be " ++ show wee ++ ", not " ++ show s)
  pure ((), ((), unders))
 where
  checkNats :: (Src, VType) -> Slice (WC (Term Chk Noun)) -> Checking ()
  checkNats tgt (These xs) = mapM_ (check1Under tgt) xs
  checkNats tgt (From x) = check1Under tgt x

  bigEndPred :: Slice (WC (Term Chk Noun)) -> Checking (Int -> Bool)
  bigEndPred (These []) = pure (const True) -- We can always select to nothing
  bigEndPred (These xs) = do vs <- mapM (evalNat . unWC) xs
                             let biggest = foldr1 max vs
                             pure (>biggest)
  bigEndPred (From x) = evalNat (unWC x) >>= \n -> pure (>= n)

  weeEnd :: Slice (WC (Term Chk Noun)) -> Int -> Checking Int
  weeEnd (These xs) _ = pure $ length xs
  weeEnd (From x) t = do n <- evalNat (unWC x)
                         pure (t - n)

  checkSlice :: (Int -> Bool) -> Checking ()
  checkSlice p = do s <- evalNat s
                    t <- evalNat t
                    unless
                      (s <= t)
                      (fail $ "Slice: " ++ show s ++ " is bigger than " ++ show t)
                    if p t
                      then pure ()
                      else fail "check bad slice bad sorry"

-- Need to think about selecting from things other than vectors?
check' (Select from slice) ((), (_, Vector ty n):unders) = do
  ([(_, Vector ty' n')], ((), ())) <- check from ((), ())
  unless (ty == ty') (fail "types no match")
  node <- next "thinning type" Hypo [] []
  check1Under ((node, "th"), n :<<<: n') slice
  pure ((), ((), unders))
check' (Pattern p) ((), (tgt:unders))
 = checkRPat tgt (unWC p) $> ((), ((), unders))
check' (Let abs x y) conn = do
  (dangling, ((), ())) <- check x ((), ())
  venv <- abstractAll dangling (unWC abs)
  localVEnv venv $ check y conn
check' t _ = fail $ "Won't check " ++ show t

-- Check a pattern used as a constructor (on the Rhs of a definition)
checkRPat :: (Tgt, VType) -> Pattern (WC (Term Chk Noun)) -> Checking ()
-- POnePlus and PTwoTimes don't change the type of their arguments, so the
-- arguments should be able to typecheck against the type of the whole
-- expression, which may be either Nat or Int
checkRPat (tgt, ty) (POnePlus x) = do
  succ <- next (show ty ++ ".succ") (Constructor CSucc) [("value", ty)] [("value", ty)]
  noUnders $ check x ((), [((succ, "value"), ty)])
  wire ((succ, "value"), Right ty, tgt)
  pure ()
checkRPat (tgt, ty) (PTwoTimes x) = do
  doub <- next (show ty ++ ".doub") (Constructor CDoub) [("value", ty)] [("value", ty)]
  noUnders $ check x ((), [((doub, "value"), ty)])
  wire ((doub, "value"), Right ty, tgt)
  pure ()
checkRPat (_, List _) PNil = pure ()
-- A `cons` on the RHS contain a single variable or application that produces
-- two outputs (head and tail), so typecheck it as such with as normal
checkRPat (tgt, List ty) (PCons b) = do
  cons <- next "List.cons" (Constructor CCons) [("head", ty), ("tail", List ty)] [("value", List ty)]
  noUnders $ check b ((), [((cons, "head"), ty), ((cons, "tail"), List ty)])
  wire ((cons, "value"), Right (List ty), tgt)
  pure ()
checkRPat (_, vty@(Vector _ n)) p@PNil = do
  hypo <- next "Vec.size" Hypo [("ty", SimpleTy Natural)] []
  check' n ((), [((hypo, "ty"), SimpleTy Natural)])

  len <- evalNat n
  if len == 0
    then pure ()
    else err $ VecLength len (show vty) "0" (show p)
checkRPat (tgt, vty@(Vector ty n)) (PCons b) = do
  hypo <- next "Vec.size" Hypo [("ty", SimpleTy Natural)] []
  check' n ((), [((hypo, "ty"), SimpleTy Natural)])

  len <- evalNat n
  when (len <= 0)
    (err $ VecLength len (show vty) "(> 0)" (show (PCons b)))

  let tailTy = Vector ty (Simple (Num (len - 1)))
  cons <- next "Vec.cons" (Constructor CCons)
          [("head", ty), ("tail", tailTy)]
          [("value", Vector ty n)]
  noUnders $
    check b ((), [((cons, "head"), ty)
                 ,((cons, "tail"), tailTy)])
  wire ((cons, "value"), Right (Vector ty n), tgt)
  pure ()

checkRPat (_, Option _) PNone = pure ()
checkRPat (tgt, Option ty) (PSome x) = do
  some <- next "Option.some" (Constructor CSome) [("value", ty)] [("value", Option ty)]
  noUnders $ check x ((), [((some, "value"), ty)])
  wire ((some, "value"), Right (Option ty), tgt)
  pure ()
checkRPat unders pat = typeErr $ show pat ++ " not of type " ++ show unders

check1Under :: (Tgt, VType) -> WC (Term Chk Noun) -> Checking ()
check1Under tgt tm = noUnders (check tm ((), [tgt])) >>= \((),()) -> pure ()

abstractAll :: (EnvFor e aType) => [(Src, aType)]
            -> Abstractor
            -> Checking (Env e)
abstractAll stuff binder = do
  (env, unders) <- abstract stuff binder
  ensureEmpty "unders after abstract" unders
  pure env

abstract :: (EnvFor e aType) => [(Src, aType)]
         -> Abstractor
         -> Checking (Env e -- Local env for checking body of lambda
                     ,[(Src, aType)] -- rightovers
                     )
abstract [] abs = err $ NothingToBind (show abs)
abstract (input:inputs) (Bind x) = pure (singletonEnv x input, inputs)
abstract inputs (x :||: y) = do
  (venv, inputs)  <- abstract inputs x
  (venv', inputs) <- abstract inputs y
  (,inputs) <$> mergeEnvs [venv, venv']
abstract inputs (APull ports abst) = do
  inputs <- pullPorts ports inputs
  abstract inputs abst
abstract inputs@((_,ty):_) pat@(Pat abs) = case abstractPattern inputs abs of
  Just res -> res
  Nothing -> err (PattErr $
    "Couldn't resolve pattern " ++ show pat ++ " with type " ++ show ty)
abstract ((_, ty):inputs) (Lit tm) = case bindToLit ty of
  Left desc -> typeErr $ "Can't match literal " ++ show tm ++ desc
  Right ty -> simpleCheck ty tm $> (emptyEnv, inputs)
abstract (input:inputs) (VecLit xs) = (,inputs) <$> abstractVecLit input xs


run :: (VEnv, [Decl], FC)
    -> Checking a
    -> Either Error (a, ([TypedHole], Graph))
run (ve, ds, fc) m = let ctx = Ctx { venv = ve
                                   , decls = ds
                                   , typeFC = fc
                                   } in
                       (\(a,b,_) -> (a,b)) <$> handler m ctx root


kcheck :: TensorOutputs (Outputs Kernel d)
      => WC (Term d k)
      -> Connectors Kernel d k
      -> Checking (Outputs Kernel d
                  ,Connectors Kernel d k)
kcheck (WC fc tm) conn = localFC fc $ kcheck' tm conn

kcheck' :: TensorOutputs (Outputs Kernel d)
       => Term d k
       -> Connectors Kernel d k
       -> Checking (Outputs Kernel d
                   ,Connectors Kernel d k) -- rightovers
kcheck' (s :|: t) tys = do
  (outs, tys)  <- kcheck s tys
  (outs', tys) <- kcheck t tys
  outs <- tensor outs outs'
  pure (outs, tys)
kcheck' (s :-: t) (overs, unders) = do
  (overs, (rightovers, ())) <- kcheck s (overs, ())
  (outs,  (emptyOvers, rightunders)) <- kcheck t (overs, unders)
  ensureEmpty "overs" emptyOvers
  pure (outs, (rightovers, rightunders))
kcheck' (binder :\: body) (overs, unders) = do
  (ext, overs) <- abstract overs (unWC binder)
  (outs, ((), unders)) <- localKVar ext $ kcheck body ((), unders) <* req KDone
  pure (outs, (overs, unders))
kcheck' (Pull ports t) (overs, unders) = do
  unders <- pullPorts ports unders
  kcheck t (overs, unders)
kcheck' (Emb t) (overs, unders) = do
  (outs, (overs, ())) <- kcheck t (overs, ())
  unders <- checkOutputs t unders outs
  pure ((), (overs, unders))
kcheck' (Th _) _ = fail "no higher order signals! (Th)"
kcheck' (Var x) ((), ()) = req (KLup x) >>= \case
  Just output -> pure ([output], ((), ()))
  Nothing -> err $ KVarNotFound (show x)
-- TODO: find a way to make check perceive this as a function
-- Check brat functions and arguments assuming they'll produce a kernel
kcheck' (fun :$: arg) ((), ())
  | Var f <- unWC fun = do
     -- traceM $ "Looking for " ++ show f
     req (VLup f) >>= \case
       Just [(src, (K (R ss) (R ts)))] -> trace "kernel" $ kernel src ss ts
       -- The following pattern avoids crashing and produces better error messages for ill-typed programs (only)
       Just [(src, (C (ss :-> ts)))] -> function src f ss ts
       Just _ -> typeErr "Left of an application isn't function-like"
       Nothing -> err $ VarNotFound (show f)

-- Check applications of kernels
  | otherwise = do
  (tys, ((), ())) <- check fun ((), ())
  (src, ss, ts) <- case tys of
                     {- TODO:
                       This logic is not flexible enough:
                        - What if there's more than 2 kernels?
                        - What if there's three kernels but the arg is 2 qubits?
                        - Ultimately kernels need to behave more like normal functions
                     -}
                     [(src, K (R ss) (R ts)), (_, K (R us) (R vs))] -> pure (src, (ss <> us), (ts <> vs))
                     ((src, K (R ss) (R ts)):_) -> pure (src, ss, ts)
                     _ -> typeErr "BRAT function called from kernel"
  evalNode <- knext "eval" (Eval src) ss ts
  ((), ((), emptyUnders)) <- kcheck arg ((), [((evalNode, port), ty) | (port, ty) <- ss])
  ensureEmpty "unders" emptyUnders
  pure ([ ((evalNode, port), ty) | (port, ty) <- ts], ((), ()))
   where
     function src f ss ts = do
      funNode  <- next ("eval_" ++ show f) (Eval src) ss ts
      ((), ()) <- noUnders $ check arg ((), [ ((funNode, port), ty) | (port, ty) <- ss ])
      let tys = [ ((funNode, port), ty) | (port, ty) <- ts ]
      (src, ss, ts) <- case tys of
                         [(src, K (R ss) (R ts)), (_, K (R us) (R vs))] -> pure (src, (ss <> us), (ts <> vs))
                         ((src, K (R ss) (R ts)):_) -> pure (src, ss, ts)
                         _ -> typeErr "BRAT function called from kernel"
      evalNode <- knext "eval" (Eval src) ss ts
      ((), ()) <- noUnders $ kcheck arg ((), [((evalNode, port), ty) | (port, ty) <- ss])
      pure ([ ((evalNode, port), ty) | (port, ty) <- ts], ((), ()))


     kernel src ss ts = do
       evalNode <- knext "eval" (Eval src) ss ts
       ((), ()) <- noUnders $ kcheck arg ((), [((evalNode, port), ty) | (port, ty) <- ss])
       pure ([ ((evalNode, port), ty) | (port, ty) <- ts], ((), ()))


kcheck' (NHole name) ((), unders) = do
  fc <- req AskFC
  req $ LogHole $ NKHole name fc ((), unders)
  pure ((), ((), []))
kcheck' (VHole name) (overs, unders) = do
  fc <- req AskFC
  req $ LogHole $ VKHole name fc (overs, unders)
  pure ((), ([], []))
kcheck' tm@(Vec elems) ((), (tgt, vty@(Of ty n)):unders) = do
  hypo <- next "Vec.size" Hypo [("ty", SimpleTy Natural)] []
  fc   <- req AskFC
  check1Under ((hypo, "ty"), SimpleTy Natural) (WC fc n)

  len <- evalNat n
  unless (length elems == len)
    (err $ VecLength len (show vty) (show $ length elems) (show tm))
  let inputs = [('e':show i, ty) | i <- [0..(len-1)]]
  mkvec <- knext "mkvec" (Constructor CVec) inputs [("value", Of ty n)]
  sequence_ [noUnders $ kcheck x ((), [((mkvec, p), ty)])
            | (x, (p,ty)) <- zip elems inputs]
  wire ((mkvec, "value"), Left (Of ty n), tgt)
  pure ((), ((), unders))

kcheck' (Pattern p) ((), ((tgt, vty@(Of ty n)):unders))
 | PNil <- unWC p = do
     hypo <- next "Vec.size" Hypo [("ty", SimpleTy Natural)] []
     noUnders $ check' n ((), [((hypo, "ty"), SimpleTy Natural)])
     n <- evalNat n
     if n == 0
       then pure ((), ((), unders))
       else err $ VecLength n (show vty) "0" (show (unWC p))
 | PCons x <- unWC p = do
     hypo <- next "Vec.size" Hypo [("ty", SimpleTy Natural)] []
     noUnders $ check' n ((), [((hypo, "ty"), SimpleTy Natural)])
     n <- evalNat n
     when (n <= 0)
       (err $ VecLength n (show vty) "> 0" (show (PCons x)))

     cons <- knext "Vec.cons" (Constructor CCons)
             [("head", ty), ("tail", Of ty (Simple (Num (n - 1))))]
             [("value", Of ty (Simple (Num n)))]

     noUnders $
       kcheck x ((), [((cons,"head"), ty)
                     ,((cons,"tail"), Of ty (Simple (Num (n - 1))))])
     wire ((cons,"value"), Left (Of ty (Simple (Num n))), tgt)
     pure ((), ((), unders))
kcheck' (Let abs x y) conn = do
  (dangling, ((), ())) <- kcheck x ((), ())
  kenv <- abstractAll dangling (unWC abs)
  localKVar kenv $ kcheck y conn
kcheck' (Simple (Bool _)) ((), ((_, Bit):unders)) = pure ((), ((), unders))
kcheck' t _ = fail $ "Won't kcheck " ++ show t
