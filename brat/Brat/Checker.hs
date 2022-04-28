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
                    ) where

import Control.Arrow ((***))
import Control.Monad (unless, when, foldM)
import Control.Monad.Freer
import qualified Control.Monad.Fail as Fail
import Data.Functor (($>))
import Data.Kind (Type)
import Data.List (intercalate, transpose)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude

import Brat.Error
import Brat.Eval
import Brat.FC
import Brat.Graph
import Brat.Naming
import Brat.Search
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.UserName

import Debug.Trace

type Graph = Graph' Term
type Node = Node' Term
type Wire = Wire' Term

type family Overs (m :: Mode) (k :: Kind) :: Type where
  Overs m Noun = ()
  Overs m Verb = [(Src, ValueType m)]

type family Unders (m :: Mode) (d :: Dir) :: Type where
  Unders m Syn = ()
  Unders m Chk = [(Tgt, ValueType m)]

type family Outputs (m :: Mode) (d :: Dir) :: Type where
  Outputs m Syn = [(Src, ValueType m)]
  Outputs m Chk = ()

class Combine a where
  combine :: a -> a -> Checking a

instance Combine [(Src, VType)] where
  combine [(src, C (ss :-> ts))] [(src', C (us :-> vs))] = do
    node <- next (show src ++ ", " ++ show src') (Combo src src') (ss <> us) (ts <> vs)
    pure [((node, "fun"), C ((ss <> us) :-> (ts <> vs)))]
  combine a b = pure $ a <> b

instance Combine [(Src, SType)] where
  combine a b = pure $ a <> b

instance Combine () where
  combine () () = pure ()

class (Show t) => AType t where
  anext :: String -> Thing -> [(Port, t)] -> [(Port, t)] -> Checking Name
  makeVec :: t -> Term Chk Noun -> t
  bindToLit :: t -> Either String SimpleType -- Left is error description

instance AType SType where
  anext = knext
  makeVec = Of
  bindToLit Bit = Right Boolean
  bindToLit _ = Left " in a kernel"

instance AType VType where
  anext = next
  makeVec = Vector
  bindToLit (SimpleTy ty) = Right ty
  bindToLit _ = Left ""

type Connectors (m :: Mode) (d :: Dir) (k :: Kind) = (Overs m k, Unders m d)

data Mode = Brat | Kernel

type family ValueType (m :: Mode) where
  ValueType Brat = VType
  ValueType Kernel = SType

type VEnv = [(UserName, [(Src, VType)])]
type KEnv = M.Map UserName (Quantity, (Src, SType))

class EnvLike env where
  mergeEnvs :: [env] -> Checking env
  emptyEnv :: env

instance EnvLike VEnv where
  mergeEnvs = pure . concat -- TODO make this check for disjointness like KEnv's do
  emptyEnv = []

instance EnvLike KEnv where
  mergeEnvs = foldM combineDisjointKEnvs M.empty
  emptyEnv = M.empty

class (EnvLike env, AType ty) => EnvFor env ty where
  singletonEnv :: String -> (Src, ty) -> env
  abstractPattern :: [(Src, ty)] -> Pattern Abstractor -> Maybe (Checking (env, [(Src, ty)]))
  abstractVecLit :: (Src, ty) -> [Abstractor] -> Checking env

instance EnvFor VEnv VType where
  singletonEnv x input = [(plain x, [input])]
  abstractPattern inputs@((_, SimpleTy Natural):_) (POnePlus (Bind x)) = Just $ abstract inputs (Bind x)
  abstractPattern inputs@((_, SimpleTy Natural):_) (PTwoTimes (Bind x)) = Just $ abstract inputs (Bind x)
  abstractPattern ((_, List _):inputs) PNil = Just $ pure ([], inputs)
  abstractPattern ((_, List ty):inputs) (PCons (x :||: xs)) = Just $ do
    node <- next "PCons (List)" Hypo [("head", ty), ("tail", List ty)] []
    venv <- abstractAll [((node, "head"), ty)] x
    venv' <- abstractAll [((node, "tail"), List ty)] xs
    pure (venv ++ venv', inputs)
  abstractPattern ((src, Option ty):inputs) (PSome x) = Just $ abstract ((src, ty):inputs) x
  abstractPattern ((_, Option _):inputs) PNone = Just $ pure ([], inputs)
  abstractPattern ((_, vty@(Vector ty n)):inputs) abs = Just $ (,inputs) <$> abstractVecPat (ty, n) vty abs
  abstractPattern _ _ = Nothing

  abstractVecLit (_, Vector ty n) abss = abstractVecLitVec (ty, n) abss

  abstractVecLit (_, List ty) xs = do
    node <- next "List literal pattern" Hypo [("type", ty)] []
    venvs <- mapM (abstractAll [((node, "type"), ty)]) xs
    pure $ concat venvs

  abstractVecLit (src, Product l r) [a,b] = do
    venv <- abstractAll [(src, l)] a
    venv' <- abstractAll [(src, r)] b
    pure (venv ++ venv')

  abstractVecLit _ xs = err $ PattErr $ "Can't bind to Vector Literal " ++ (show xs)

instance EnvFor KEnv SType where
  singletonEnv x input@(_, ty) =
    let q = if copyable ty then Tons else One
    in M.singleton (plain x) (q, input)
  abstractPattern ((_, vty@(Of ty n)):inputs) abs = Just $ (,inputs) <$> abstractVecPat (ty, n) vty abs
  abstractPattern _ _ = Nothing
  abstractVecLit ((_, Of ty n)) abss = abstractVecLitVec (ty, n) abss
  abstractVecLit _ xs = err $ PattErr $ "Can't bind to Vector Literal " ++ (show xs) ++ " in kernel"

abstractVecPat :: (EnvFor env aType) => (aType, Term Chk Noun)
               -> aType -- for error message
               -> Pattern Abstractor
               -> Checking env
abstractVecPat (_, n) vty p@PNil = evalNatSoft n >>= \case
  Right 0 -> pure emptyEnv
  -- If we can't work out what the size is, it might be 0
  Left _  -> pure emptyEnv
  Right n -> err $ VecLength n (show vty) "0" (show p)
abstractVecPat (ty, n) _ (PCons (x :||: xs)) = do
  -- A `cons` pattern on the LHS needs to have exactly two binders
  n <- evalNat n
  let tailTy = makeVec ty (Simple (Num (n - 1)))
  node <- anext "PCons (Vec)" Hypo [("head", ty), ("tail", tailTy)] []
  venv <- abstractAll [((node, "head"), ty)] x
  venv' <- abstractAll [((node, "tail"), tailTy)] xs
  mergeEnvs [venv,venv']

abstractVecLitVec :: (EnvFor env aType) => (aType, Term Chk Noun)
                  -> [Abstractor]
                  -> Checking env
abstractVecLitVec (ty, n) xs = do
    node <- next "natHypo" Hypo [] [("value", SimpleTy Natural)]
    check' n ((), [((node, "value"), SimpleTy Natural)])
    n <- evalNat n
    unless (n == length xs)
      (fail $ "length mismatch in vector pattern")
    envs <- mapM (abstractAll [((node, "type"), ty)]) xs
    mergeEnvs envs

data TypedHole
  = NBHole Name FC [String] (Connectors Brat Chk Noun)
  | VBHole Name FC (Connectors Brat Chk Verb)
  | NKHole Name FC (Connectors Kernel Chk Noun)
  | VKHole Name FC (Connectors Kernel Chk Verb)
  deriving (Eq, Show)

err :: ErrorMsg -> Checking a
err msg = do
  fc <- req AskFC
  req $ Throw $ Err (Just fc) Nothing msg

typeErr :: String -> Checking a
typeErr = err . TypeErr

showRow :: Show ty => [(Src, ty)] -> String
showRow xs = intercalate ", " [ '(':p ++ " :: " ++ show ty ++ ")"
                              | ((_, p), ty) <- xs]

data Context = Ctx { venv :: VEnv
                   , decls :: [Decl]
                   , typeFC :: FC
                   }

data CheckingSig ty where
  Fresh   :: String -> CheckingSig Name
  Throw   :: Error  -> CheckingSig a
  LogHole :: TypedHole -> CheckingSig ()
  AskFC   :: CheckingSig FC
  VLup    :: UserName -> CheckingSig (Maybe [(Src, VType)])
  KLup    :: UserName -> CheckingSig (Maybe (Src, SType))
  Node    :: Node -> CheckingSig ()
  Wire    :: Wire -> CheckingSig ()
  Decls   :: CheckingSig [Decl]
  KDone   :: CheckingSig ()
  AskVEnv :: CheckingSig VEnv

data Quantity = None | One | Tons

qpred :: Quantity -> Maybe Quantity
qpred None = Nothing
qpred One  = Just None
qpred Tons = Just Tons

ensureEmpty :: Show ty => String -> [(Src, ty)] -> Checking ()
ensureEmpty _ [] = pure ()
ensureEmpty str xs = err $ InternalError $ "Expected empty " ++ str ++ ", got:\n  " ++ showRow xs

-- Run a type-checking computation, and ensure that what comes back is a classical thunk
-- TODO: this should be able to work on kernels too
onlyThunk :: Checking (Outputs Brat Syn, Connectors Brat Syn Noun)
          -> Checking (Src, [Input], [Output])
onlyThunk m = do
  (outs, ((), ())) <- m
  let tys = [ (p, ty) | ((_, p), ty) <- outs ]
  src <- case outs of
           (((src, _), _):_) -> pure src
           [] -> err $ InternalError "Expected a thunk, but found nothing!"
  case merge tys of
    [(port, C (ss :-> ts))] -> pure ((src,port), ss, ts)
    _ -> err $ ExpectedThunk (showRow outs)

noUnders m = do
  (outs, (overs, unders)) <- m
  ensureEmpty "unders" unders
  pure (outs, overs)

localFC :: FC -> Checking v -> Checking v
localFC _ (Ret v) = Ret v
localFC f (Req AskFC k) = localFC f (k f)
localFC f (Req r k) = Req r (localFC f . k)

localVEnv :: VEnv -> Checking v -> Checking v
localVEnv _   (Ret v) = Ret v
localVEnv ext (Req (VLup x) k) | Just x <- lookup x ext = localVEnv ext (k (Just x))
localVEnv ext (Req AskVEnv k) = do env <- req AskVEnv
                                   localVEnv ext (k (ext ++ env))
localVEnv ext (Req r k) = Req r (localVEnv ext . k)

wrapError :: (Error -> Error) -> Checking v -> Checking v
wrapError _ (Ret v) = Ret v
wrapError f (Req (Throw e) k) = Req (Throw (f e)) k
wrapError f (Req r k) = Req r (wrapError f . k)

vlup :: UserName -> Checking [(Src, VType)]
vlup s = do
  req (VLup s) >>= \case
    Just vty -> pure vty
    Nothing -> err $ VarNotFound (show s)

lookupAndUse :: UserName -> KEnv -> Either Error (Maybe ((Src, SType), KEnv))
lookupAndUse x kenv = case M.lookup x kenv of
   Nothing -> Right Nothing
   Just (q, rest) -> case qpred q of
                      Nothing -> Left $ Err Nothing Nothing $ TypeErr $ (show x) ++ " has already been used"
                      Just q -> Right $ Just (rest, M.insert x (q, rest) kenv)

localKVar :: KEnv -> Free CheckingSig v -> Free CheckingSig v
localKVar _   (Ret v) = Ret v
localKVar env (Req (KLup x) k) = case lookupAndUse x env of
                                   Left err@(Err (Just _) _ _) -> req $ Throw err
                                   Left (Err Nothing _ msg) -> err msg
                                   Right (Just (th, env)) -> localKVar env (k (Just th))
                                   Right Nothing -> Req (KLup x) (localKVar env . k)
localKVar env (Req KDone k) = case [ x | (x,(One,_)) <- M.assocs env ] of
                                [] -> (localKVar env . k) ()
                                xs -> typeErr $
                                      unwords ["Variable(s)"
                                              ,intercalate ", " (fmap show xs)
                                              ,"haven't been used"
                                              ]
localKVar env (Req r k) = Req r (localKVar env . k)

handler :: Free CheckingSig v
        -> Context
        -> Namespace
        -> Either Error (v,([TypedHole],Graph),Namespace)
handler (Ret v) _ ns = return (v, mempty, ns)
handler (Req s k) ctx ns
  = case s of
      Fresh str -> let (name, root) = fresh str ns in
                     handler (k name) ctx root
      Throw err -> Left err
      LogHole hole -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                         return (v,(hole:holes,g),ns)
      AskFC -> handler (k (typeFC ctx)) ctx ns
      VLup s -> handler (k $ lookup s (venv ctx)) ctx ns
      Node n -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                   return (v,(holes,([n],[]) <> g),ns)
      Wire w -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                   return (v,(holes,([],[w]) <> g),ns)
      Decls ->  handler (k (decls ctx)) ctx ns
      -- We only get a KLup here if the variable has not been found in the kernel context
      KLup _ -> handler (k Nothing) ctx ns
      -- Receiving KDone may become possible when merging the two check functions
      KDone -> error "KDone in handler - this shouldn't happen"
      AskVEnv -> handler (k (venv ctx)) ctx ns

type Checking = Free CheckingSig

-- This way we get file contexts when pattern matching fails
instance {-# OVERLAPPING #-} Fail.MonadFail Checking where
  fail = typeErr

next :: String -> Thing -> [Input] -> [Output] -> Checking Name
next str th ins outs = do
  this <- req (Fresh str)
  () <- req (Node (BratNode this th ins outs))
  pure this

knext :: String -> Thing -> [(Port, SType)] -> [(Port, SType)] -> Checking Name
knext str th ins outs = do
  this <- req (Fresh str)
  () <- req (Node (KernelNode this th ins outs))
  pure this

wire :: Wire -> Checking ()
wire w = req $ Wire w

ceval :: Term Chk k -> Checking (Either Error Value)
ceval tm = do env <- req Decls
              fc <- req AskFC
              pure $ evalTerm env (WC fc tm)

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

check :: Combine (Outputs Brat d)
      => WC (Term d k)
      -> Connectors Brat d k
      -> Checking (Outputs Brat d
                  ,Connectors Brat d k)
check (WC fc tm) conn = localFC fc (check' tm conn)

check' :: Combine (Outputs Brat d)
      => Term d k
      -> Connectors Brat d k
      -> Checking (Outputs Brat d
                  ,Connectors Brat d k) -- rightovers
check' (s :|: t) tys = do
  (outs, tys)  <- check s tys
  (outs', tys) <- check t tys
  outs <- combine outs outs'
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
  unders <- checkOutputs unders outs
  pure ((), (overs, unders))
 where
  checkOutputs :: [(Tgt, VType)] -> [(Src, VType)] -> Checking [(Tgt, VType)]
  checkOutputs tys [] = pure tys
  -- HACK: Try to merge kernels willy-nilly
  checkOutputs top@((_, K _ _):_) ((src, K (R ss) (R ts)):(src', K (R us) (R vs)):outs) = do
    src <- next "kcombo" (Combo src src') [] [("fun", K (R (ss <> us)) (R (ts <> vs)))]
    checkOutputs top (((src, "fun"), K (R (ss <> us)) (R (ts <> vs))):outs)
  checkOutputs ((tgt, ty):tys) ((src, ty'):outs)
   | ty == ty' = wire (src, Right ty, tgt) *> checkOutputs tys outs
  checkOutputs tgt src = let exp = showRow tgt
                             act = showRow src
                         in  err $ TypeMismatch (show t) exp act

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
check' (Vec [a,b]) ((), (_, Product s t):unders) = do
  unpack <- next "pairCheck" Hypo [] [("first", s), ("second", t)]
  check1 ((unpack, "first"), s) a
  check1 ((unpack, "second"), t) b
  pure ((), ((), unders))
check' (Vec elems) ((), (_, vty@(Vector ty n)):unders) = do
  hypo <- next "nat hypo" Hypo [] []
  fc <- req AskFC
  check1 ((hypo, "ty"), SimpleTy Natural) (WC fc n)

  hypo <- next "vec type hypo" Hypo [] []
  mapM_ (aux [((hypo, "ty"), ty)]) elems

  ceval n >>= \case
    Left err -> req $ Throw err
    Right (VSimple (Num n)) -> if length elems == n
                               then pure ((), ((), unders))
                               else err $ VecLength n (show vty) (show $ length elems) (show $ Vec elems)
    Right v -> fail $ unwords ["Trying to reduce", show n, "but got", show v]
 where
  aux :: [(Src, VType)] -> WC (Term Chk Noun) -> Checking ()
  aux ty tm = do
    ((), ()) <- noUnders (check tm ((), ty))
    pure ()

check' (Vec elems) ((), (_, List ty):unders) = do
  hypo <- next "list type hypo" Hypo [] [("type", ty)]
  mapM_ (aux hypo . unWC) elems
  pure ((), ((), unders))
 where
  aux :: Name -> Term Chk Noun -> Checking ()
  aux hypo e = do
    ((), ()) <- noUnders (check' e ((), [((hypo, "type"), ty)]))
    pure ()

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
    env <- req $ AskVEnv
    let matches = transpose $
          [ [ (nm, src) | (src, _) <- stuff ]
          | (nm, stuff) <- env
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
  check1 ((natHyp, "weeEnd"), SimpleTy Natural) (WC fc s)
  check1 ((natHyp, "bigEnd"), SimpleTy Natural) (WC fc t)
  check1 ((natHyp, "bigEnd2"), SimpleTy Natural) big
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
  checkNats tgt (These xs) = mapM_ (check1 tgt) xs
  checkNats tgt (From x) = check1 tgt x

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
  check1 ((node, "th"), n :<<<: n') slice
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
checkRPat tgt (POnePlus x) = check1 tgt x
checkRPat tgt (PTwoTimes x) = check1 tgt x
checkRPat (_, List _) PNil = pure ()
-- A `cons` on the RHS contain a single variable or application that produces
-- two outputs (head and tail), so typecheck it as such with as normal
checkRPat (tgt, List ty) (PCons b)
  = () <$ noUnders (check b ((), [(tgt, ty), (tgt, List ty)]))
checkRPat (_, vty@(Vector _ n)) p@PNil = do
  n <- evalNat n
  if n == 0
    then pure ()
    else err $ VecLength n (show vty) "0" (show p)
checkRPat (tgt, vty@(Vector ty n)) (PCons b) = do
  n <- evalNat n
  when (n <= 0)
    (err $ VecLength n (show vty) "(> 0)" (show (PCons b)))
  noUnders $
    check b ((), [(tgt, ty)
                 ,(tgt, Vector ty (Simple (Num (n - 1))))])
  pure ()

checkRPat (_, Option _) PNone = pure ()
checkRPat (tgt, Option ty) (PSome x) = check1 (tgt, ty) x
checkRPat unders pat = typeErr $ show pat ++ " not of type " ++ show unders

check1 :: (Tgt, VType) -> WC (Term Chk Noun) -> Checking ()
check1 tgt tm = do
  ((), ()) <- noUnders (check tm ((), [tgt]))
  pure ()

simpleCheck :: SimpleType -> SimpleTerm -> Checking ()
simpleCheck Natural (Num n) | n >= 0 = pure ()
simpleCheck IntTy (Num _) = pure ()
simpleCheck Boolean (Bool _) = pure ()
simpleCheck FloatTy (Float _) = pure ()
simpleCheck TextType (Text _) = pure ()
simpleCheck UnitTy Unit = pure ()
simpleCheck ty tm = fail (unwords [show tm, "is not of type", show ty])

evalNatSoft :: Term Chk Noun -> Checking (Either String Int)
evalNatSoft tm = ceval tm >>= \case
  Right (VSimple (Num n)) -> pure (Right n)
  Right v -> pure (Left $ unwords ["Trying to reduce", show tm, "but got", show v])
  Left err -> req $ Throw err

evalNat :: Term Chk Noun -> Checking Int
evalNat tm = evalNatSoft tm >>= \case
  Right n -> pure n
  Left er -> typeErr er

abstractAll :: (EnvFor aEnv aType) => [(Src, aType)]
            -> Abstractor
            -> Checking aEnv
abstractAll stuff binder = do
  (env, unders) <- abstract stuff binder
  ensureEmpty "unders after abstract" unders
  pure env

abstract :: (EnvFor aEnv aType) => [(Src, aType)]
         -> Abstractor
         -> Checking (aEnv -- Local env for checking body of lambda
                     , [(Src, aType)] -- rightovers
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
abstract _ x = typeErr $ "Can't abstract " ++ show x

combineDisjointKEnvs :: KEnv -> KEnv -> Checking KEnv
combineDisjointKEnvs l r =
  let commonKeys = S.intersection (M.keysSet l) (M.keysSet r)
  in if S.null commonKeys
    then Ret $ M.union l r
    else typeErr ("Variable(s) defined twice: " ++
      (intercalate "," $ map show $ S.toList commonKeys))

pullPorts :: [Port] -> [((Name, Port), ty)] -> Checking [((Name, Port), ty)]
pullPorts [] types = pure types
pullPorts (p:ports) types = do
  (x, types) <- pull1Port p types
  (x:) <$> pullPorts ports types
 where
  pull1Port :: Port -> [((Name, Port), ty)]
            -> Checking (((Name, Port), ty), [((Name, Port), ty)])
  pull1Port p [] = fail $ "Port not found: " ++ p
  pull1Port p (x@((_, p'), _):xs)
   | p == p' = pure (x, xs)
   | otherwise = (id *** (x:)) <$> pull1Port p xs

run :: (VEnv, [Decl], FC)
    -> Checking a
    -> Either Error (a, ([TypedHole], Graph))
run (ve, ds, fc) m = let ctx = Ctx { venv = ve
                                   , decls = ds
                                   , typeFC = fc
                                   } in
                       (\(a,b,_) -> (a,b)) <$> handler m ctx root


kcheck :: Combine (Outputs Kernel d)
      => WC (Term d k)
      -> Connectors Kernel d k
      -> Checking (Outputs Kernel d
                  ,Connectors Kernel d k)
kcheck (WC fc tm) conn = localFC fc $ kcheck' tm conn

kcheck' :: Combine (Outputs Kernel d)
       => Term d k
       -> Connectors Kernel d k
       -> Checking (Outputs Kernel d
                   ,Connectors Kernel d k) -- rightovers
kcheck' (s :|: t) tys = do
  (outs, tys)  <- kcheck s tys
  (outs', tys) <- kcheck t tys
  outs <- combine outs outs'
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
  unders <- kcheckOutputs unders outs
  pure ((), (overs, unders))
 where
  kcheckOutputs :: [(Tgt, SType)] -> [(Src, SType)] -> Checking [(Tgt, SType)]
  kcheckOutputs tys [] = pure tys
  kcheckOutputs ((tgt, ty):tys) ((src, ty'):outs)
   | ty == ty' = wire (src, Left ty, tgt) *> kcheckOutputs tys outs
  kcheckOutputs _ _ = fail "check (kernel): checkOutputs failed"
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
kcheck' tm@(Vec elems) ((), (_, vty@(Of ty n)):unders) = do
  hypo <- next "nat hypo" Hypo [] []
  fc   <- req AskFC
  check1 ((hypo, "ty"), SimpleTy Natural) (WC fc n)

  hypo <- next "vec type hypo" Hypo [] []
  mapM_ (aux [((hypo, "ty"), ty)]) elems

  ceval n >>= \case
    Left err -> req $ Throw err
    Right (VSimple (Num n)) -> if length elems == n
                               then pure ((), ((), unders))
                               else err $ VecLength n (show vty) (show $ length elems) (show tm)
    Right v -> fail $ unwords ["Trying to reduce", show n, "but got", show v]
 where
  aux :: [(Src, SType)] -> WC (Term Chk Noun) -> Checking ()
  aux ty tm = do
    ((), ()) <- noUnders (kcheck tm ((), ty))
    pure ()
kcheck' (Pattern p) ((), ((tgt, vty@(Of ty n)):unders))
 | PNil <- unWC p = do
     n <- evalNat n
     if n == 0
       then pure ((), ((), unders))
       else err $ VecLength n (show vty) "0" (show (unWC p))
 | PCons x <- unWC p = do
     n <- evalNat n
     when (n <= 0)
       (err $ VecLength n (show vty) "> 0" (show (PCons x)))
     noUnders $
       kcheck x ((), [(tgt, ty)
                    ,(tgt, Of ty (Simple (Num (n - 1))))])
     pure ((), ((), unders))
kcheck' (Simple (Bool _)) ((), ((_, Bit):unders)) = pure ((), ((), unders))
kcheck' t _ = fail $ "Won't kcheck " ++ show t
