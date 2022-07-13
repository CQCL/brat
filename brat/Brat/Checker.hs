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
                    ,checkOutputs
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

singletonEnv :: (?my :: Modey m) => String -> (Src, ValueType m) -> Env (EnvData m)
singletonEnv x input@(_, ty) = case ?my of
  Braty -> M.singleton (plain x) [input]
  Kerny -> let q = if copyable ty then Tons else One
           in  M.singleton (plain x) (q, input)


abstractVecLit :: (Show (ValueType m), (?my :: Modey m))
               => (Src, ValueType m)
               -> [Abstractor]
              -> Checking (Env (EnvData m))
abstractVecLit (src, ty) abs
  | Just (ty, n) <- getVec ?my ty = do
      node <- next "natHypo" Hypo [("value", SimpleTy Natural)] []
      let ?my = Braty in check' n ((), [((node, "value"), SimpleTy Natural)])
      n <- evalNat n
      unless (n == length abs)
        (err $ VecPatLength (show abs) (show (makeVec ty (Simple (Num n)))))
      envs <- mapM (abstractAll [((node, "type"), ty)]) abs
      mergeEnvs envs
  | otherwise = case (?my, ty, abs) of
    (Braty, List ty, abss) -> do
        node <- next "List literal pattern" Hypo [("type", ty)] []
        venvs <- mapM (abstractAll [((node, "type"), ty)]) abss
        mergeEnvs venvs
    (Braty, Product l r, [a,b]) -> do
        venv <- abstractAll [(src, l)] a
        venv' <- abstractAll [(src, r)] b
        combineDisjointEnvs venv venv'
    _ -> err $ PattErr $ "Can't bind to Vector Literal " ++ (show abs) ++ (showMode ?my)


-- Run a type-checking computation, and ensure that what comes back
-- is a classical thunk or kernel as appropriate for `mode`
onlyThunk :: (?my :: Modey m)
          => Checking (Outputs Brat Syn, Connectors Brat Syn Noun)
          -> Checking (Src, [(Port, ValueType m)], [(Port, ValueType m)])
onlyThunk comp = do
  (outs, ((), ())) <- comp
  outs1 <- case outs of
    [] -> err $ ExpectedThunk (showMode ?my) "empty row"
    x:xs -> pure (x :| xs)
  rows <- combinationsWithLeftovers outs1
  let (out, emptyUnders) = last rows
  ensureEmpty "unders" emptyUnders
  case (?my, out) of
    (Braty, (src, C (ss :-> ts))) -> pure (src, ss, ts)
    (Kerny, (src, K (R ss) (R ts))) -> pure (src, ss, ts)
    _ -> err $ ExpectedThunk (showMode ?my) (showRow (out :| []))

-- Allows joining the outputs of two nodes together into a `Combo` node
vtensor :: (?my :: Modey m) => [(Src, ValueType m)] -> [(Src, ValueType m)] -> Checking [(Src, ValueType m)]
vtensor ss [] = pure ss
vtensor [] ts = pure ts
vtensor ss ts = do
  let sig = mergeSigs (rowToSig ss) (rowToSig ts)
  tensorNode <- anext "tensor" (Combo Row) sig sig
  mapM (\((src,ty),dstPort) -> awire (src,ty,(tensorNode,dstPort)))
       (zip (ss ++ ts) (map fst sig))
  pure $ sigToRow tensorNode sig

class TensorOutputs d where
  tensor :: d -> d -> Checking d

instance TensorOutputs () where
  tensor () () = pure ()

instance TensorOutputs [(Src, VType)] where
 tensor = let ?my = Braty in vtensor

instance TensorOutputs [(Src, SType)] where
 tensor = let ?my = Kerny in vtensor

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

type CheckConstraints m =
  (SubtractThunks (ValueType m)
  ,Eq (ValueType m)
  ,Show (ValueType m)
  ,TensorOutputs (Outputs m Syn)
  ,TensorOutputs (Outputs m Chk)
  )

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
  checkCombination :: (CheckConstraints m, ?my :: Modey m)
                => Src -> [(Port, ValueType m)] -> [(Port, ValueType m)] -> VType
                -> Checking ()
  checkCombination src ins outs fty = do
    source <- anext "src" Source [] ins
    target <- anext "tgt" Target outs []
    -- The box is always a `Brat` `Thing` (classical)
    box <- next ("eval(" ++ show src ++ ")") (source :>>: target) [] [("fun", fty)]
    ((), (emptyOvers, emptyUnders)) <- check tm (sigToRow box ins, sigToRow box outs)
    ensureEmpty "overs" emptyOvers 
    ensureEmpty "unders" emptyUnders

  -- Split on the type to determine in which mode to `checkCombination`
  tryToCheckThunk :: (Src, VType) -> Checking ()
  tryToCheckThunk (src, ty) = case ty of
    C (ss :-> ts) -> let ?my = Braty in checkCombination src ss ts ty
    K (R ss) (R ts) -> let ?my = Kerny in checkCombination src ss ts ty
    _ -> typeErr "Not a function type"

checkOutputs :: (CheckConstraints m, ?my :: Modey m)
             => WC (Term Syn k)
             -> [(Tgt, ValueType m)]
             -> [(Src, ValueType m)]
             -> Checking [(Tgt, ValueType m)]
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
checkClauses (NoLhs verb) conn = let ?my = Braty in check verb conn
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
   in let ?my = Braty in check (WC (FC (start lfc) (end rfc)) (lhs :\: rhs))

check :: (CheckConstraints m, TensorOutputs (Outputs m d), ?my :: Modey m)
      => WC (Term d k)
      -> Connectors m d k
      -> Checking (Outputs m d
                  ,Connectors m d k)
check (WC fc tm) conn = localFC fc (check' tm conn)

check' :: (CheckConstraints m, TensorOutputs (Outputs m d), ?my :: Modey m)
       => Term d k
       -> Connectors m d k
       -> Checking (Outputs m d
                   ,Connectors m d k) -- rightovers
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
  (ext, overs) <- abstract overs (unWC binder)
  (outs, ((), unders)) <- localEnv ext $ check body ((), unders)
  pure (outs, (overs, unders))
check' (Pull ports t) (overs, unders) = do
  unders <- pullPorts ports unders
  check t (overs, unders)
check' (t ::: outs) (overs, ()) | Braty <- ?my = do
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
check' (Th t) conns = case ?my of
  Braty -> let ((), unders) = conns in ((),) . ((),) <$> checkThunk t unders
  Kerny -> typeErr "no higher order signals! (Th)"
check' (Var x) ((), ()) = case ?my of
  Braty -> (, ((), ())) <$> vlup x
  Kerny -> req (KLup x) >>= \case
    Just output -> pure ([output], ((), ()))
    Nothing -> err $ KVarNotFound (show x)
check' (fun :$: arg) ((), ()) = do
  (src, ss, ts) <- onlyThunk $ let ?my = Braty in check fun ((), ())
  evalNode <- anext "eval" (Eval src) ss ts
  ((), ()) <- noUnders $ check arg ((), sigToRow evalNode ss)
  pure (sigToRow evalNode ts, ((), ()))
check' (Vec elems) ((), (tgt, vty):unders) | Just (ty, n) <- getVec ?my vty = do
  size <- next "vec.size" Hypo [("value", SimpleTy Natural)] []
  fc <- req AskFC
  let ?my = Braty in check1Under ((size, "value"), SimpleTy Natural) (WC fc n)
  len <- evalNat n
  unless (length elems == len)
    (err $ VecLength len (show vty) (show (length elems)) (show elems))
  let inputs = [('e':show i,ty) | i <- [0..(len-1)]]
  mkvec <- anext "mkvec" (Constructor CVec) inputs [("value", vty)]
  sequence_ [noUnders $ check x ((), [((mkvec, p), ty)]) | (x, (p, ty)) <- zip elems inputs]
  awire ((mkvec, "value"), vty, tgt)
  pure ((), ((), unders))
check' (Pattern p) ((), (tgt:unders))
 = checkRPat tgt (unWC p) $> ((), ((), unders))
check' (Let abs x y) conn = do
  (dangling, ((), ())) <- check x ((), ())
  env <- abstractAll dangling (unWC abs)
  localEnv env $ check y conn
check' (NHole name) ((), unders) = req AskFC >>= \fc -> case ?my of
  Kerny -> do
    req $ LogHole $ NKHole name fc ((), unders)
    pure ((), ((), []))
  Braty -> do
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
  req $ LogHole $ case ?my of
    Braty -> VBHole name fc (overs, unders)
    Kerny -> VKHole name fc (overs, unders)
  pure ((), ([], []))
check' t c = case (?my, t, c) of -- remaining cases need to split on ?my
  (Kerny, Simple (Bool _), ((), ((_, Bit):unders))) -> pure ((), ((), unders))
  (Braty, Simple tm, ((), ((src, p), SimpleTy ty):unders)) -> do
    simpleCheck ty tm
    this <- next (show tm) (Const tm) [] [("value", SimpleTy ty)]
    wire ((this, "value"), SimpleTy ty, (src, p))
    pure ((), ((), unders))
  (Braty, Vec [a,b], ((), (tgt, Product s t):unders)) -> do
    mkpair <- anext "mkpair" (Constructor CPair) [("first", s), ("second", t)] [("value", Product s t)]
    check1Under ((mkpair, "first"), s) a
    check1Under ((mkpair, "second"), t) b
    wire ((mkpair, "value"), (Product s t), tgt)
    pure ((), ((), unders))
  (Braty, Vec elems, ((), (tgt, List ty):unders)) -> do
    let inputs = [('e':show i, ty) | (i,_) <- zip [0..] elems]
    mklist <- next "mklist" (Constructor CList) inputs [("value", List ty)]
    sequence_ [noUnders $ check x ((), [((mklist, p), ty)]) | (x, (p, ty)) <- zip elems inputs]
    wire ((mklist,"value"), List ty, tgt)
    pure ((), ((), unders))
  (Braty, Slice big slice, ((), (_, s :<<<: t):unders)) -> do
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
    bigEndPred (These xs) = mapM (evalNat . unWC) xs >>= \xs -> pure (>(foldr1 max xs))
    bigEndPred (From x) = evalNat (unWC x) >>= \n -> pure (>= n)

    weeEnd :: Slice (WC (Term Chk Noun)) -> Int -> Checking Int
    weeEnd (These xs) _ = pure $ length xs
    weeEnd (From x) t = evalNat (unWC x) >>= \n -> pure (t - n)

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
  (Braty, Select from slice, ((), (_, Vector ty n):unders)) -> do
    ([(_, Vector ty' n')], ((), ())) <- check from ((), ())
    unless (ty == ty') (fail "types no match")
    node <- next "thinning type" Hypo [] []
    check1Under ((node, "th"), n :<<<: n') slice
    pure ((), ((), unders))
  (_, t, _) -> typeErr $ "Won't check " ++ (showMode ?my) ++ show t


-- Check a pattern used as a constructor (on the Rhs of a definition)
checkRPat :: (CheckConstraints m, ?my :: Modey m) => (Tgt, ValueType m) -> Pattern (WC (Term Chk Noun)) -> Checking ()
checkRPat (_, vty) p@PNil | Just (_, n) <- getVec ?my vty = do
  hypo <- next "Vec.size" Hypo [("value", SimpleTy Natural)] []
  noUnders $ let ?my = Braty in check' n ((), [((hypo, "value"), SimpleTy Natural)])

  len <- evalNat n
  when (len /= 0) (err $ VecLength len (show vty) "0" (show p))
checkRPat (tgt, vty) p@(PCons b) | Just (ty, n) <- getVec ?my vty = do
  hypo <- next "Vec.size" Hypo [("value", SimpleTy Natural)] []
  noUnders $ let ?my = Braty in check' n ((), [((hypo, "value"), SimpleTy Natural)])

  len <- evalNat n
  when (len <= 0)
    (err $ VecLength len (show vty) "(> 0)" (show p))

  let inps = [("head", ty), ("tail", makeVec ty (Simple (Num (len - 1))))]
  cons <- anext "Vec.cons" (Constructor CCons) inps [("value", vty)]
  noUnders $ check b ((), sigToRow cons inps)
  awire ((cons, "value"), vty, tgt)
  pure ()
checkRPat unders pat = case (?my, unders, pat) of
  -- POnePlus and PTwoTimes don't change the type of their arguments, so the
  -- arguments should be able to typecheck against the type of the whole
  -- expression, which may be either Nat or Int
  (Braty, (tgt, ty), POnePlus x) -> do
    succ <- next (show ty ++ ".succ") (Constructor CSucc) [("value", ty)] [("value", ty)]
    noUnders $ check x ((), [((succ, "value"), ty)])
    wire ((succ, "value"), ty, tgt)
    pure ()
  (Braty, (tgt, ty), PTwoTimes x) -> do
    doub <- next (show ty ++ ".doub") (Constructor CDoub) [("value", ty)] [("value", ty)]
    noUnders $ check x ((), [((doub, "value"), ty)])
    wire ((doub, "value"), ty, tgt)
    pure ()
  (Braty, (_, List _), PNil) -> pure ()
  -- A `cons` on the RHS contain a single variable or application that produces
  -- two outputs (head and tail), so typecheck it as such with as normal
  (Braty, (tgt, List ty), PCons b) -> do
    cons <- next "List.cons" (Constructor CCons) [("head", ty), ("tail", List ty)] [("value", List ty)]
    noUnders $ check b ((), [((cons, "head"), ty), ((cons, "tail"), List ty)])
    wire ((cons, "value"), List ty, tgt)
    pure ()
  (Braty, (_, Option _), PNone) -> pure ()
  (Braty, (tgt, Option ty), PSome x) -> do
    some <- next "Option.some" (Constructor CSome) [("value", ty)] [("value", Option ty)]
    noUnders $ check x ((), [((some, "value"), ty)])
    wire ((some, "value"), Option ty, tgt)
    pure ()
  _ -> typeErr $ show pat ++ " not of type " ++ show unders

check1Under :: (CheckConstraints m, ?my :: Modey m) => (Tgt, ValueType m) -> WC (Term Chk Noun) -> Checking ()
check1Under tgt tm = noUnders (check tm ((), [tgt])) >>= \((),()) -> pure ()

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
abstract [] abs = err $ NothingToBind (show abs)
abstract (input:inputs) (Bind x) = pure (singletonEnv x input, inputs)
abstract inputs (x :||: y) = do
  (venv, inputs)  <- abstract inputs x
  (venv', inputs) <- abstract inputs y
  (,inputs) <$> mergeEnvs [venv, venv']
abstract inputs (APull ports abst) = do
  inputs <- pullPorts ports inputs
  abstract inputs abst
abstract inputs@((_,ty):inputs') pat@(Pat abs)
  | Just (ety, n) <- getVec ?my ty =
    (evalNat n) >>= \n -> (,inputs') <$> case abs of
      PNil -> if n == 0
        then pure emptyEnv
        else err $ VecLength n (show ty) "0" (show abs)
      PCons (x :||: xs) -> do
        -- A `cons` pattern on the LHS needs to have exactly two binders
        let tailTy = makeVec ety (Simple (Num (n - 1)))
        node <- anext "PCons (Vec)" Hypo [("head", ety), ("tail", tailTy)] []
        venv <- abstractAll [((node, "head"), ety)] x
        venv' <- abstractAll [((node, "tail"), tailTy)] xs
        mergeEnvs [venv,venv'] 
      _ -> err $ NotVecPat (show abs) (show ty)
  | otherwise = case (?my, inputs) of
    (Braty, inputs@((src,ty):inputs')) | Just result <- abstractBrat ty abs -> result
      where
        abstractBrat :: VType -> (Pattern Abstractor) -> Maybe (Checking (VEnv, [(Src, VType)]))
        abstractBrat ty abs = case (ty, abs) of
          (SimpleTy Natural, POnePlus (Bind x)) -> Just $ abstract inputs (Bind x)
          (SimpleTy Natural, PTwoTimes (Bind x)) -> Just $ abstract inputs (Bind x)
          (List _, PNil) -> Just $ pure (emptyEnv, inputs')
          (List ty, (PCons (x :||: xs))) -> Just $ do
            node <- next "PCons (List)" Hypo [("head", ty), ("tail", List ty)] []
            venv <- abstractAll [((node, "head"), ty)] x
            venv' <- abstractAll [((node, "tail"), List ty)] xs
            (,inputs') <$> combineDisjointEnvs venv venv'
          (Option ty, PSome x) -> Just $ abstract ((src, ty):inputs') x
          (Option _, PNone) -> Just $ pure (emptyEnv, inputs')
          _ -> Nothing
    _ -> err (PattErr $
      "Couldn't resolve pattern " ++ show pat ++ " with type " ++ show ty)
abstract ((_, ty):inputs) (Lit tm) = do
  litTy <- case (?my,ty) of
    (Kerny, Bit) -> pure $ Boolean
    (Braty, SimpleTy ty) -> pure $ ty
    (m,_) -> typeErr $ "Can't match literal literal " ++ show tm ++ (showMode m)
  simpleCheck litTy tm $> (emptyEnv, inputs)
abstract (input:inputs) (VecLit xs) = (,inputs) <$> abstractVecLit input xs


run :: (VEnv, [Decl], FC)
    -> Checking a
    -> Either Error (a, ([TypedHole], Graph))
run (ve, ds, fc) m = let ctx = Ctx { venv = ve
                                   , decls = ds
                                   , typeFC = fc
                                   } in
                       (\(a,b,_) -> (a,b)) <$> handler m ctx root
