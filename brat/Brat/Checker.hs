{-# LANGUAGE
ConstraintKinds,
FlexibleContexts,
MultiParamTypeClasses
#-}

module Brat.Checker (check
                    ,run
                    ,VEnv
                    ,Checking
                    ,Connectors
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

type CheckConstraints m =
  (SubtractThunks (ValueType m)
  ,EnvFor (EnvData m) (ValueType m)
  ,Eq (ValueType m)
  ,Show (ValueType m)
  )

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
    check' Braty n ((), [((node, "value"), SimpleTy Natural)])
    n <- evalNat n
    unless (n == length xs)
      (err $ VecPatLength (show xs) (show (makeVec ty (Simple (Num n)))))
    envs <- mapM (abstractAll [((node, "type"), ty)]) xs
    mergeEnvs envs

-- Run a type-checking computation, and ensure that what comes back
-- is a classical thunk or kernel as appropriate for `mode`
onlyThunk :: Modey m
          -> Checking (Outputs Brat Syn, Connectors Brat Syn Noun)
          -> Checking (Src, [(Port, ValueType m)], [(Port, ValueType m)])
onlyThunk mode comp = do
  (outs, ((), ())) <- comp
  outs1 <- case outs of
    [] -> err $ ExpectedThunk (showMode mode) "empty row"
    x:xs -> pure (x :| xs)
  rows <- combinationsWithLeftovers outs1
  let (out, emptyUnders) = last rows
  ensureEmpty "unders" emptyUnders
  case getThunk mode out of
    Just res -> pure res
    Nothing  -> err $ ExpectedThunk (showMode mode) (showRow (out :| []))
 where
  getThunk :: Modey m -> (Src, VType) -> Maybe (Src, [(Port, ValueType m)], [(Port, ValueType m)])
  getThunk Braty (src, C (ss :-> ts)) = pure (src, ss, ts)
  getThunk Kerny (src, K (R ss) (R ts)) = pure (src, ss, ts)
  getThunk _ _ = Nothing


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

checkThunk :: WC (Term Chk Verb) -> Unders Brat Chk -> Checking (Unders Brat Chk)
checkThunk _ [] = err $ InternalError "checkThunk called with empty unders"
checkThunk tm (u:us) =
  combinationsWithLeftovers (u :| us) >>= aux
 where
  aux ((ty, lo) :| opts) = (catchErr $ tryToCheckThunk ty) >>= \case
    Right () -> pure lo -- success
    Left err -> case opts of
         -- option failed; try another, or throw last error
         -- TODO: rollback any nodes/wires generated by failure
      [] -> req (Throw err)
      (h:t) -> aux (h :| t)

  -- Type check a thunk against a single combination type, return void for success
  checkCombination :: CheckConstraints m
                => Modey m
                -> Src -> [(Port, ValueType m)] -> [(Port, ValueType m)] -> VType
                -> Checking ()
  checkCombination m src ins outs fty = do
    source <- anext "src" Source [] ins
    target <- anext "tgt" Target outs []
    -- The box is always a `Brat` `Thing` (classical)
    box <- next ("eval(" ++ show src ++ ")") (source :>>: target) [] [("fun", fty)]
    ((), (emptyOvers, emptyUnders)) <- check m tm (sigToRow box ins, sigToRow box outs)
    ensureEmpty "overs" emptyOvers 
    ensureEmpty "unders" emptyUnders

  -- Split on the type to determine in which mode to `checkCombination`
  tryToCheckThunk :: (Src, VType) -> Checking ()
  tryToCheckThunk (src, ty) = case ty of
    C (ss :-> ts) -> checkCombination Braty src ss ts ty
    K (R ss) (R ts) -> checkCombination Kerny src ss ts ty
    _ -> typeErr "Not a function type"

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
checkClauses (NoLhs verb) conn = check Braty verb conn
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
   in  check Braty (WC (FC (start lfc) (end rfc)) (lhs :\: rhs))

check :: (CheckConstraints m, TensorOutputs (Outputs m d))
      => Modey m
      -> WC (Term d k)
      -> Connectors m d k
      -> Checking (Outputs m d
                  ,Connectors m d k)
check m (WC fc tm) conn = localFC fc (check' m tm conn)

check' :: (CheckConstraints m, TensorOutputs (Outputs m d))
       => Modey m
       -> Term d k
       -> Connectors m d k
       -> Checking (Outputs m d
                   ,Connectors m d k) -- rightovers
check' m (s :|: t) tys = do
  -- in Checking mode, each LHS/RHS removes the wires/types it produces from the Unders remaining,
  -- including components of thunks joined together by (Combo Thunk)s in checkOutputs
  (outs, tys)  <- check m s tys
  (outs', tys) <- check m t tys
  -- in Synthesizing mode, instead we join together the outputs here
  -- with a (Combo Row), although the latter node may not be useful
  outs <- tensor outs outs'
  pure (outs, tys)
check' m (s :-: t) (overs, unders) = do
  (overs, (rightovers, ())) <- check m s (overs, ())
  (outs,  (emptyOvers, rightunders)) <- check m t (overs, unders)
  ensureEmpty "overs" emptyOvers
  pure (outs, (rightovers, rightunders))
check' m (binder :\: body) (overs, unders) = do
  (ext, overs) <- abstract overs (unWC binder)
  (outs, ((), unders)) <- localEnv m ext $ check m body ((), unders)
  pure (outs, (overs, unders))
check' m (Pull ports t) (overs, unders) = do
  unders <- pullPorts ports unders
  check m t (overs, unders)
check' Braty (t ::: outs) (overs, ()) = do
  (unders, dangling) <- mkIds outs
  ((), overs) <- noUnders $ check Braty t (overs, unders)
  pure (dangling, (overs, ()))
 where
  mkIds :: [Output] -> Checking ([(Tgt, VType)] -- Hungry wires
                                ,[(Src, VType)]) -- Dangling wires
  mkIds [] = pure ([], [])
  mkIds ((port, ty):outs) = do
    node <- next "id" Id [(port, ty)] [(port, ty)]
    (hungry, dangling) <- mkIds outs
    pure (((node, port), ty):hungry, ((node, port), ty):dangling)
check' m (Emb t) (overs, unders) = do
  (outs, (overs, ())) <- check m t (overs, ())
  unders <- checkOutputs t unders outs
  pure ((), (overs, unders))
check' Braty (Th t) ((), unders) = ((),) . ((),) <$> checkThunk t unders
check' Kerny (Th _) _ = typeErr "no higher order signals! (Th)"
check' Braty (Var x) ((), ()) = do
  output <- vlup x
  pure (output, ((), ()))
check' Kerny (Var x) ((), ()) = req (KLup x) >>= \case
  Just output -> pure ([output], ((), ()))
  Nothing -> err $ KVarNotFound (show x)
check' m (fun :$: arg) ((), ()) = do
  (src, ss, ts) <- onlyThunk m $ check Braty fun ((), ())
  evalNode <- anext "eval" (Eval src) ss ts
  ((), ()) <- noUnders $ check m arg ((), [((evalNode, port), ty) | (port, ty) <- ss])
  pure ([ ((evalNode, port), ty) | (port, ty) <- ts], ((), ()))
check' Braty (Simple tm) ((), ((src, p), SimpleTy ty):unders) = do
  simpleCheck ty tm
  this <- next (show tm) (Const tm) [] [("value", SimpleTy ty)]
  wire ((this, "value"), Right (SimpleTy ty), (src, p))
  pure ((), ((), unders))
check' Kerny (Simple (Bool _)) ((), ((_, Bit):unders)) = pure ((), ((), unders))
check' Braty (Vec [a,b]) ((), (tgt, Product s t):unders) = do
  mkpair <- next "mkpair" (Constructor CPair) [("first", s), ("second", t)] [("value", Product s t)]
  check1Under Braty ((mkpair, "first"), s) a
  check1Under Braty ((mkpair, "second"), t) b
  wire ((mkpair, "value"), Right (Product s t), tgt)
  pure ((), ((), unders))
check' m (Vec elems) ((), (tgt, vty):unders) | Just (ty, n) <- getVec m vty = do
  size <- next "vec.size" Hypo [("value", SimpleTy Natural)] []
  fc <- req AskFC
  check1Under Braty ((size, "value"), SimpleTy Natural) (WC fc n)
  len <- evalNat n
  unless (length elems == len)
    (err $ VecLength len (show vty) (show (length elems)) (show elems))
  let inputs = [('e':show i,ty) | i <- [0..(len-1)]]
  mkvec <- anext "mkvec" (Constructor CVec) inputs [("value", vty)]
  sequence_ [noUnders $ check m x ((), [((mkvec, p), ty)]) | (x, (p, ty)) <- zip elems inputs]
  awire ((mkvec, "value"), vty, tgt)
  pure ((), ((), unders))
check' Braty (Vec elems) ((), (tgt, List ty):unders) = do
  let inputs = [('e':show i, ty) | (i,_) <- zip [0..] elems]
  mklist <- next "mklist" (Constructor CList) inputs [("value", List ty)]
  sequence_ [noUnders $ check Braty x ((), [((mklist, p), ty)]) | (x, (p, ty)) <- zip elems inputs]
  wire ((mklist,"value"), Right (List ty), tgt)
  pure ((), ((), unders))
check' Braty (NHole name) ((), unders) = do
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

check' Kerny (NHole name) ((), unders) = do
  fc <- req AskFC
  req $ LogHole $ NKHole name fc ((), unders)
  pure ((), ((), []))
check' m (VHole name) (overs, unders) = do
  fc <- req AskFC
  req $ LogHole $ case m of
    Braty -> VBHole name fc (overs, unders)
    Kerny -> VKHole name fc (overs, unders)
  pure ((), ([], []))
check' Braty (Slice big slice) ((), (_, s :<<<: t):unders) = do
  natHyp <- next "slice check" Hypo [] []
  fc <- req AskFC
  check1Under Braty ((natHyp, "weeEnd"), SimpleTy Natural) (WC fc s)
  check1Under Braty ((natHyp, "bigEnd"), SimpleTy Natural) (WC fc t)
  check1Under Braty ((natHyp, "bigEnd2"), SimpleTy Natural) big
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
  checkNats tgt (These xs) = mapM_ (check1Under Braty tgt) xs
  checkNats tgt (From x) = check1Under Braty tgt x

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
check' Braty (Select from slice) ((), (_, Vector ty n):unders) = do
  ([(_, Vector ty' n')], ((), ())) <- check Braty from ((), ())
  unless (ty == ty') (fail "types no match")
  node <- next "thinning type" Hypo [] []
  check1Under Braty ((node, "th"), n :<<<: n') slice
  pure ((), ((), unders))
check' m (Pattern p) ((), (tgt:unders))
 = checkRPat m tgt (unWC p) $> ((), ((), unders))
check' m (Let abs x y) conn = do
  (dangling, ((), ())) <- check m x ((), ())
  env <- abstractAll dangling (unWC abs)
  localEnv m env $ check m y conn
check' m t _ = typeErr $ "Won't check " ++ (showMode m) ++ show t

-- Check a pattern used as a constructor (on the Rhs of a definition)
checkRPat :: CheckConstraints m => Modey m -> (Tgt, ValueType m) -> Pattern (WC (Term Chk Noun)) -> Checking ()
-- POnePlus and PTwoTimes don't change the type of their arguments, so the
-- arguments should be able to typecheck against the type of the whole
-- expression, which may be either Nat or Int
checkRPat Braty (tgt, ty) (POnePlus x) = do
  succ <- next (show ty ++ ".succ") (Constructor CSucc) [("value", ty)] [("value", ty)]
  noUnders $ check Braty x ((), [((succ, "value"), ty)])
  wire ((succ, "value"), Right ty, tgt)
  pure ()
checkRPat Braty (tgt, ty) (PTwoTimes x) = do
  doub <- next (show ty ++ ".doub") (Constructor CDoub) [("value", ty)] [("value", ty)]
  noUnders $ check Braty x ((), [((doub, "value"), ty)])
  wire ((doub, "value"), Right ty, tgt)
  pure ()
checkRPat Braty (_, List _) PNil = pure ()
-- A `cons` on the RHS contain a single variable or application that produces
-- two outputs (head and tail), so typecheck it as such with as normal
checkRPat Braty (tgt, List ty) (PCons b) = do
  cons <- next "List.cons" (Constructor CCons) [("head", ty), ("tail", List ty)] [("value", List ty)]
  noUnders $ check Braty b ((), [((cons, "head"), ty), ((cons, "tail"), List ty)])
  wire ((cons, "value"), Right (List ty), tgt)
  pure ()
checkRPat m (_, vty) p@PNil = case getVec m vty of
  Just (_, n) -> do
    hypo <- next "Vec.size" Hypo [("value", SimpleTy Natural)] []
    noUnders $ check' Braty n ((), [((hypo, "value"), SimpleTy Natural)])

    len <- evalNat n
    when (len /= 0) (err $ VecLength len (show vty) "0" (show p))
  Nothing -> typeErr $ "Checking literal 'Nil' against non-vector type: " ++ show vty
checkRPat m (tgt, vty) p@(PCons b) = case getVec m vty of
  Just (ty, n) -> do
    hypo <- next "Vec.size" Hypo [("value", SimpleTy Natural)] []
    noUnders $ check' Braty n ((), [((hypo, "value"), SimpleTy Natural)])

    len <- evalNat n
    when (len <= 0)
      (err $ VecLength len (show vty) "(> 0)" (show (PCons b)))

    let inps = [("head", ty), ("tail", makeVec ty (Simple (Num (len - 1))))]
    cons <- anext "Vec.cons" (Constructor CCons) inps [("value", vty)]
    noUnders $ check m b ((), sigToRow cons inps)
    awire ((cons, "value"), vty, tgt)
    pure ()
  Nothing -> typeErr $ "Checking 'cons' expr: " ++ show p ++ " against non-vector type: " ++ show vty
checkRPat Braty (_, Option _) PNone = pure ()
checkRPat Braty (tgt, Option ty) (PSome x) = do
  some <- next "Option.some" (Constructor CSome) [("value", ty)] [("value", Option ty)]
  noUnders $ check Braty x ((), [((some, "value"), ty)])
  wire ((some, "value"), Right (Option ty), tgt)
  pure ()
checkRPat _ unders pat = typeErr $ show pat ++ " not of type " ++ show unders

check1Under :: CheckConstraints m => Modey m -> (Tgt, ValueType m) -> WC (Term Chk Noun) -> Checking ()
check1Under m tgt tm = noUnders (check m tm ((), [tgt])) >>= \((),()) -> pure ()

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
