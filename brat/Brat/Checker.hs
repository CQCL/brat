{-# LANGUAGE FlexibleContexts #-}

module Brat.Checker (check
                    ,pp
                    ,run
                    ,VEnv
                    ,CEnv
                    ,Checking
                    ,Connectors
                    ,Graph
                    ,Mode(..)
                    ,Node(..)
                    ,CheckingSig(..)
                    ,checkClauses
                    ,TypedHole(..)
                    ,Wire
                    ,wire
                    ,wrapError
                    ,next, knext
                    ,localFC
                    ,withPrefix
                    ) where

import Control.Arrow ((***))
import Control.Monad (unless, when)
import Control.Monad.Freer
import qualified Control.Monad.Fail as Fail
import Data.Functor (($>))
import Data.Kind (Type)
import Data.List (intercalate, transpose)
import Data.List.NonEmpty (NonEmpty(..))
import Prelude

import Brat.Error
import Brat.Eval
import Brat.FC
import Brat.Graph
import Brat.Naming
import Brat.Search
import Brat.Syntax.Common
import Brat.Syntax.Core

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

instance Combine [(Src, SType Term)] where
  combine a b = pure $ a <> b

instance Combine () where
  combine () () = pure ()

type Connectors (m :: Mode) (d :: Dir) (k :: Kind) = (Overs m k, Unders m d)

data Mode = Brat | Kernel deriving (Eq, Show)

type family ValueType (m :: Mode) where
  ValueType Brat = VType
  ValueType Kernel = SType Term

type CEnv = [(String, CType)]
type VEnv = [(String, (Src, VType))]

data TypedHole
  = NBHole Name FC [String] (Connectors Brat Chk Noun)
  | VBHole Name FC (Connectors Brat Chk Verb)
  | NKHole Name FC (Connectors Kernel Chk Noun)
  | VKHole Name FC (Connectors Kernel Chk Verb)
  deriving (Eq, Show)

newtype Barf a = Barf { runBarf :: Either Error a }
 deriving (Applicative, Functor, Monad, Show)

dumbErr :: String -> Error
dumbErr = Err Nothing Nothing . TypeErr

err :: String -> Checking a
err msg = do
  fc <- req AskFC
  req $ Throw $ Err (Just fc) Nothing $ TypeErr msg

instance MonadFail Barf where
  fail s = Barf . Left . Err Nothing Nothing $ TypeErr s

data Context = Ctx { cenv :: CEnv
                   , venv :: VEnv
                   , ndecls :: [NDecl]
                   , vdecls :: [VDecl]
                   , typeFC :: FC
                   , stack :: [Term Syn Noun]
                   } deriving Show

data CheckingSig ty where
  Fresh   :: String -> CheckingSig Name
  Split   :: String -> CheckingSig Namespace
  Throw   :: Error  -> CheckingSig a
  LogHole :: TypedHole -> CheckingSig ()
  AskFC   :: CheckingSig FC
  VLup    :: String -> CheckingSig (Maybe (Src, VType))
  CLup    :: String -> CheckingSig (Maybe CType)
  Node    :: Node -> CheckingSig ()
  Wire    :: Wire -> CheckingSig ()
  Decls   :: CheckingSig ([NDecl], [VDecl])
  KLup    :: String -> CheckingSig (Src, SType Term)
  KDone   :: CheckingSig ()
  AskVEnv :: CheckingSig VEnv

data Quantity = None | One | Tons deriving (Eq, Show)

qpred :: Quantity -> Maybe Quantity
qpred None = Nothing
qpred One  = Just None
qpred Tons = Just Tons

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

localCEnv :: CEnv -> Checking v -> Checking v
localCEnv _   (Ret v) = Ret v
localCEnv ext (Req (CLup x) k) | Just x <- lookup x ext = localCEnv ext (k (Just x))
localCEnv ext (Req r k) = Req r (localCEnv ext . k)

wrapError :: (Error -> Error) -> Checking v -> Checking v
wrapError f (Ret v) = Ret v
wrapError f (Req (Throw e) k) = Req (Throw (f e)) k
wrapError f (Req r k) = Req r (wrapError f . k)

vlup :: String -> Checking (Src, VType)
vlup s = do
  fc <- req AskFC
  req (VLup s) >>= \case
    Just vty -> pure vty
    Nothing -> err $ s ++ " not in (value) environment"

clup :: String -> Checking CType
clup s = do
  fc <- req AskFC
  req (CLup s) >>= \case
    Just cty -> pure cty
    Nothing -> err $ s ++ " not in (computation) environment"

type KEnv = [(String, (Quantity, (Src, SType Term)))]

lookupAndUse :: String -> KEnv -> Either Error (Maybe ((Src, SType Term), KEnv))
lookupAndUse _ [] = Right Nothing
lookupAndUse x (curr@(y, (q, rest)):kenv)
  | x == y = case qpred q of
               Nothing -> Left $ Err Nothing Nothing $ TypeErr $ x ++ " has already been used"
               Just q -> Right $ Just (rest, (x, (q, rest)):kenv)
  | otherwise = case lookupAndUse x kenv of
                  Left err -> Left err
                  Right (Just (thing, kenv)) -> Right $ Just (thing, curr:kenv)
                  Right Nothing -> Right Nothing

localKVar :: [(String, (Quantity, (Src, SType Term)))] -> Free CheckingSig v -> Free CheckingSig v
localKVar _   (Ret v) = Ret v
localKVar env (Req (KLup x) k) = case lookupAndUse x env of
                                   Left err@(Err (Just _) _ _) -> req $ Throw err
                                   Left (Err Nothing src msg) -> do
                                     fc <- req AskFC
                                     req $ Throw (Err (Just fc) src msg)
                                   Right (Just (th, env)) -> localKVar env (k th)
                                   Right Nothing -> Req (KLup x) (localKVar env . k)
localKVar env (Req KDone k) = case [ x | (x,(One,_)) <- env ] of
                                [] -> (localKVar env . k) ()
                                xs -> err $ unwords ["Variable(s)"
                                                    ,intercalate ", " xs
                                                    ,"haven't been used"
                                                    ]
localKVar env (Req r k) = Req r (localKVar env . k)

withPrefix :: String -> Checking v -> Checking v
withPrefix str m = do
  ns <- req $ Split str
  prefixHandler ns m
 where
  prefixHandler :: Namespace -> Checking v -> Checking v
  prefixHandler _ (Ret x) = Ret x
  prefixHandler pre (Req (Fresh str) k) = let (nm, ns) = fresh str pre in
                                            (prefixHandler ns $ k nm)
  prefixHandler pre (Req r k) = Req r (prefixHandler pre . k)

handler :: Free CheckingSig v
        -> Context
        -> Namespace
        -> Barf (v,([TypedHole],Graph),Namespace)
handler (Ret v) _ ns = return (v, mempty, ns)
handler (Req s k) ctx ns
  = case s of
      Fresh str -> let (name, root) = fresh str ns in
                     handler (k name) ctx root
      Split str -> let (newRoot, oldRoot) = split str ns in
                     handler (k newRoot) ctx oldRoot
      Throw err -> Barf $ Left err
      LogHole hole -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                         return (v,(hole:holes,g),ns)
      AskFC -> handler (k (typeFC ctx)) ctx ns
      VLup s -> handler (k $ lookup s (venv ctx)) ctx ns
      CLup s -> handler (k $ lookup s (cenv ctx)) ctx ns
      Node n -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                   return (v,(holes,([n],[]) <> g),ns)
      Wire w -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                   return (v,(holes,([],[w]) <> g),ns)
      Decls ->  handler (k (ndecls ctx, vdecls ctx)) ctx ns
      KLup x -> fail (x ++ " not found in kernel context")
      -- Receiving KDone may become possible when merging the two check functions
      KDone -> error "KDone in handler - this shouldn't happen"
      AskVEnv -> handler (k (venv ctx)) ctx ns

type Checking = Free CheckingSig

-- This way we get file contexts when pattern matching fails
instance {-# OVERLAPPING #-} Fail.MonadFail Checking where
  fail = err

next :: String -> Thing -> [Input] -> [Output] -> Checking Name
next str th ins outs = do
  this <- req (Fresh str)
  () <- req (Node (BratNode this th ins outs))
  pure this

knext :: String -> Thing -> [(Port, SType Term)] -> [(Port, SType Term)] -> Checking Name
knext str th ins outs = do
  this <- req (Fresh str)
  () <- req (Node (KernelNode this th ins outs))
  pure this

wire :: Wire -> Checking ()
wire w = req $ Wire w

solder :: Name -> [(Src, VType)] -> [Input] -> Checking [(Src, VType)]
solder _ tys [] = pure tys
solder this ((src, ty):srcs) ((port, ty'):ins) = do
  unless (ty == ty') (fail $ "soldering unequal types: " ++ show ty ++ " and " ++ show ty')
  wire (src, Right ty, (this, port))
  solder this srcs ins
solder _ _ _ = fail "Not enough inputs"

ksolder :: Name -> [(Src, SType Term)] -> [(Port, SType Term)] -> Checking [(Src, SType Term)]
ksolder _ tys [] = pure tys
ksolder this ((src, ty):srcs) ((port, ty'):ins) = do
  unless (ty == ty') (fail $ "soldering unequal types: " ++ show ty ++ " and " ++ show ty')
  wire (src, Left ty, (this, port))
  ksolder this srcs ins
ksolder _ _ _ = fail "Not enough inputs"

ceval :: Term Chk k -> Checking (Either Error Value)
ceval tm = do env <- req Decls
              fc <- req AskFC
              pure $ evalTerm env (WC fc tm)

checkClauses :: Clause Term Verb
             -> Connectors Brat Chk Verb
             -> Checking (Outputs Brat Chk
                         ,Connectors Brat Chk Verb)
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
  checkClause (lhs, rhs)
   | lfc <- fcOf lhs
   , rfc <- fcOf rhs = check (WC (FC (start lfc) (end rfc)) (lhs :\: rhs))
   | otherwise = check' (lhs :\: rhs)

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
  (outs,  ([], rightunders)) <- check t (overs, unders)
  pure (outs, (rightovers, rightunders))
check' (binder :\: body) (overs, unders) = do
  (vext, cext, overs) <- abstract overs (unWC binder)
  (outs, ((), unders)) <- localVEnv vext $ localCEnv cext $ check body ((), unders)
  pure (outs, (overs, unders))
check' (Pull ports t) (overs, unders) = do
  unders <- pullPorts ports unders
  check t (overs, unders)
check'  (t ::: outs) (overs, ()) = do
  (unders, dangling) <- mkIds outs
  ((), (overs, [])) <- check t (overs, unders)
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
  checkOutputs top@((tgt, K _ _):tys) ((src, K (R ss) (R ts)):(src', K (R us) (R vs)):outs) = do
    src <- next "kcombo" (Combo src src') [] [("fun", K (R (ss <> us)) (R (ts <> vs)))]
    checkOutputs top (((src, "fun"), K (R (ss <> us)) (R (ts <> vs))):outs)
  checkOutputs ((tgt, ty):tys) ((src, ty'):outs)
   | ty == ty' = wire (src, Right ty, tgt) *> checkOutputs tys outs
  checkOutputs tgt src = err $ unlines ["check (brat): checkOutputs failed"
                                       ,"top: " ++ show tgt
                                       ,"bot: " ++ show src
                                       ]
check' (Th t) (overs, (tgt, ty@(C (ss :-> ts))):unders) = do
  srcNode <- next "thunk_source" Source [] ss
  tgtNode <- next "thunk_target" Target ts []
  let thOvers  = [ ((srcNode, port), ty)| (port, ty) <- ss]
  let thUnders = [ ((tgtNode, port), ty)| (port, ty) <- ts]
  fnResult <- check t (thOvers, thUnders)
  let ((), ([], [])) = fnResult
  funNode <- next "box" (srcNode :>>: tgtNode) [] [("fun", C $ ss :-> ts)]
  wire ((funNode, "fun"), Right ty, tgt)
  pure ((), (overs, unders))
check' (Th t) (overs, (tgt, ty@(K (R ss) (R ts))):unders) = do
  srcNode <- knext "thunk_source" Source [] ss
  tgtNode <- knext "thunk_target" Target ts []
  let thOvers  = [ ((srcNode, port), ty)| (port, ty) <- ss]
  let thUnders = [ ((tgtNode, port), ty)| (port, ty) <- ts]
  ((), ([], [])) <- kcheck t (thOvers, thUnders)
  funNode <- next "box" (srcNode :>>: tgtNode) [] [("fun", K (R ss) (R ts))]
  wire ((funNode, "fun"), Right ty, tgt)
  pure ((), (overs, unders))
check' (Var x) ((), ()) = do
  output <- vlup x
  pure ([output], ((), ()))
check' (Do t) (overs, ())
  | Var s <- unWC t = do
      (ss :-> ts) <- clup s
      this <- next ("Prim_" ++ s) (Prim s) ss ts
      overs <- solder this overs ss
      pure ([((this, port), ty) | (port, ty) <- ts], (overs, ()))
  | (n :|: n') <- unWC t = do
      let lfc = fcOf n
      let rfc = fcOf n
      check' ((WC lfc (Do n)) :|: (WC rfc (Do n'))) (overs, ())
  | otherwise = do
      ([(src, C (ss :-> ts))], ((), ())) <- check t ((), ())
      this <- next "eval" (Eval src) ss ts
      overs <- solder this overs ss
      pure ([ ((this, port), ty) | (port, ty) <- ts], (overs, ()))
check' (fun :$: arg) ((), ())
  | Var f <- unWC fun = do
      (node, ss, ts) <- lookupThunk f
      argResult <- check arg ((), ss)
      let ((), ((), [])) = argResult
      pure (ts, ((), ()))

  | (f :|: g) <- unWC fun, Var f <- unWC f, Var g <- unWC g = do
      (lnode, lins, louts) <- lookupThunk f
      (rnode, rins, routs) <- lookupThunk g
      argResult <- check arg ((), lins <> rins)
      let ((), ((), [])) = argResult
      pure (louts <> routs, ((), ()))

  | (f :|: g) <- unWC fun, Var f <- unWC f = do
      (lnode, lins, louts) <- lookupThunk f
      ([((src, _), C (us :-> vs))], ((), ())) <- check g ((), ())
      let rins  = [ ((src, port), ty) | (port, ty) <- us]
      let routs = [ ((src, port), ty) | (port, ty) <- vs]
      argResult <- check arg ((), lins ++ rins)
      let ((), ((), [])) = argResult
      pure (louts ++ routs, ((), ()))

  | (f :|: g) <- unWC fun, Var g <- unWC g = do
      ([((src, _), C (ss :-> ts))], ((), ())) <- check f ((), ())
      let lins  = [((src, port), ty) | (port, ty) <- ss]
      let louts = [((src, port), ty) | (port, ty) <- ts]
      (rnode, rins, routs) <- lookupThunk g
      argResult <- check arg ((), lins ++ rins)
      let ((), ((), [])) = argResult
      pure (louts ++ routs, ((), ()))

{-
  | (f :|: g) <- unWC fun = do
--      let f' = (maybe Uhh WC (fcOf f)) (Do f)
      ([((fSrc, _), C (ss :-> ts))], ((), ())) <- check f ((), ())
      ([((gSrc, _), C (us :-> vs))], ((), ())) <- check g ((), ())
      ((), ((), [])) <- check arg (()
                                  ,[ ((fSrc, port), ty) | (port, ty) <- ss ] ++
                                   [ ((gSrc, port), ty) | (port, ty) <- us ]
                                  )
      let outs = [ ((fSrc, port), ty) | (port, ty) <- ts ] ++
                 [ ((gSrc, port), ty) | (port, ty) <- vs ]

      pure (outs, ((), ()))
-}

  | otherwise = do
      traceShowM fun
      ([(src, C (ss :-> ts))], ((), ())) <- check fun ((), ())
      evalNode <- next "eval" (Eval src) ss ts
      ((), ((), [])) <- check arg ((), [((evalNode, port), ty) | (port, ty) <- ss])
      pure ([ ((evalNode, port), ty) | (port, ty) <- ts], ((), ()))
 where
  lookupThunk :: String -> Checking (Name, [(Src, VType)], [(Src, VType)])
  lookupThunk f = do
      (ss :-> ts) <- clup f
      resultNode  <- next ("prim_" ++ f) (Prim f) ss ts
      pure (resultNode
           ,([ ((resultNode, port), ty) | (port, ty) <- ss])
           ,([ ((resultNode, port), ty) | (port, ty) <- ts])
           )

check' (Simple tm) ((), ((src, p), SimpleTy ty):unders) = do
  simpleCheck ty tm
  this <- next (show tm) (Const tm) [] [("value", SimpleTy ty)]
  wire ((this, "value"), Right (SimpleTy ty), (src, p))
  pure ((), ((), unders))
check' (Pair a b) ((), (_, Product s t):unders) = do
  unpack <- next "pairCheck" Hypo [] [("first", s), ("second", t)]
  check1 ((unpack, "first"), s) a
  check1 ((unpack, "second"), t) b
  pure ((), ((), unders))
check' (Vec elems) ((), (_, Vector ty n):unders) = do
  hypo <- next "nat hypo" Hypo [] []
  fc <- req AskFC
  check1 ((hypo, "ty"), SimpleTy Natural) (WC fc n)

  hypo <- next "vec type hypo" Hypo [] []
  mapM_ (aux [((hypo, "ty"), ty)]) elems

  ceval n >>= \case
    Left (Err _ src msg) -> req AskFC >>= \fc -> req $ Throw $ Err (Just fc) src msg
    Right (VSimple (Num n)) -> if length elems == n
                               then pure ((), ((), unders))
                               else fail $ unwords ["Vector is length"
                                                   ,show (length elems)
                                                   ,"but it should be length"
                                                   ,show n
                                                   ]
    Right v -> fail $ unwords ["Trying to reduce", show n, "but got", show v]
 where
  aux ty tm = do ((), ((), [])) <- check tm ((), ty)
                 pure ()
check' (Vec elems) ((), (_, List ty):unders) = do
  hypo <- next "list type hypo" Hypo [] [("type", ty)]
  mapM_ (aux hypo . unWC) elems
  pure ((), ((), unders))
 where
  aux hypo e = do ((), ((), [])) <- check' e ((), [((hypo, "type"), ty)])
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
    let ms = intercalate ", " <$> matches
    let ss = intercalate ", " . fmap show <$> sugg
    pure $ take 5 (ms ++ ss)

  findMatchingNouns :: Checking [[String]]
  findMatchingNouns = do
    let tys = snd <$> unders
    env <- req $ AskVEnv
    traceM ("FindMatchingNouns " ++ show tys)
    let matches = traceShowId $ transpose $
          [ [ (nm, src) | (nm, (src, vty)) <- traceShowId env, vty == ty ]
          | ty <- tys
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
check' t _ = fail $ "Won't check " ++ show t

-- Check a pattern used as a constructor (on the Rhs of a definition)
checkRPat :: (Tgt, VType) -> Pattern (WC (Term Chk Noun)) -> Checking ()
checkRPat tgt@(_, SimpleTy Natural) (POnePlus x) = check1 tgt x
checkRPat tgt@(_, SimpleTy Natural) (PTwoTimes x) = check1 tgt x
checkRPat (_, List _) PNil = pure ()
checkRPat (tgt, List ty) (PCons x xs) = check1 (tgt,ty) x *> check1 (tgt, List ty) xs $> ()
checkRPat (_, Vector _ n) PNil = do
  n <- evalNat n
  if n == 0
    then pure ()
    else err "Vector length should be 0"
checkRPat (tgt, Vector ty n) (PCons x xs) = do
  n <- evalNat n
  check1 (tgt,ty) x
  when (n <= 0)
    (err $ "Vector is of length " ++ show n)
  check1 (tgt,  Vector ty (Simple (Num (n - 1)))) xs
checkRPat (_, Option ty) PNone = pure ()
checkRPat (tgt, Option ty) (PSome x) = check1 (tgt, ty) x

check1 :: (Tgt, VType) -> WC (Term Chk Noun) -> Checking ()
check1 tgt tm = do ((), ((), [])) <- check tm ((), [tgt])
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
  Left (Err _ src msg) -> req AskFC >>= \fc -> req $ Throw (Err (Just fc) src msg)

evalNat :: Term Chk Noun -> Checking Int
evalNat tm = evalNatSoft tm >>= \case
  Right n -> pure n
  Left er -> err er

abstract :: [(Src, VType)]
         -> Abstractor
         -> Checking (VEnv -- Local env for checking body of lambda
                     ,CEnv
                     ,[(Src, VType)] -- rightovers
                     )
abstract [] (Bind x) = fail $ "abstractor: no wires available to bind to " ++ show x
abstract (vty@(_, C cty):inputs) (AThunk x) = pure ([(x, vty)], [(x, cty)], inputs)
abstract (input:inputs) (Bind x) = pure ([(x, input)], [], inputs)
abstract inputs (x :||: y) = do
  (venv, cenv, inputs)  <- abstract inputs x
  (venv', cenv', inputs) <- abstract inputs y
  pure (venv ++ venv', cenv ++ cenv', inputs)
abstract inputs (APull ports abst) = do
  inputs <- pullPorts ports inputs
  abstract inputs abst
abstract ((_, SimpleTy ty):inputs) (Lit tm) = simpleCheck ty tm $> ([], [], inputs)
abstract ((_, Vector ty n):inputs) (VecLit xs) = do
  node <- next "natHypo" Hypo [] [("value", SimpleTy Natural)]
  check' n ((), [((node, "value"), SimpleTy Natural)])
  n <- evalNat n
  unless (n == length xs)
    (fail $ "length mismatch in vector pattern")
  (venvs, cenvs) <- unzip <$> mapM (aux node) xs
  pure $ (concat venvs, concat cenvs, inputs)
   where
    aux node elem = do
      (venv, cenv, []) <- abstract [((node, "type"), ty)] elem
      pure (venv, cenv)
abstract ((_, List ty):inputs) (VecLit xs) = do
    node <- next "List literal pattern" Hypo [("type", ty)] []
    (venvs, cenvs) <- unzip <$> mapM (aux node) xs
    pure $ (concat venvs, concat cenvs, inputs)
   where
    aux node elem = do
      (venv, cenv, []) <- abstract [((node, "type"), ty)] elem
      pure (venv, cenv)
abstract ((src, Product l r):inputs) (VecLit [a,b]) = do
  (venv, cenv, []) <- abstract [(src, l)] a
  (venv', cenv', []) <- abstract [(src, r)] b
  pure (venv ++ venv', cenv ++ cenv', inputs)
abstract (input:inputs) (Pat pat) = checkPat input pat
 where
  checkPat :: (Src, VType) -> Pattern Abstractor -> Checking (VEnv, CEnv, [(Src, VType)])
  checkPat (_, SimpleTy Natural) (POnePlus (Bind x)) = abstract (input:inputs) (Bind x)
  checkPat (_, SimpleTy Natural) (PTwoTimes (Bind x)) = abstract (input:inputs) (Bind x)
  checkPat (_, Vector _ n) PNil = evalNatSoft n >>= \case
    Right n -> if n == 0
               then pure ([], [], inputs)
               else err "Vector length isn't 0 for pattern `Nil`"
    -- If we can't work out what the size is, it might be 0
    Left _  -> pure ([], [], inputs)
  checkPat (_, Vector ty n) (PCons x xs) = do
    n <- evalNat n
    let tailTy = Vector ty (Simple (Num (n - 1)))
    node <- next "PCons (Vec)" Hypo [("head", ty), ("tail", tailTy)] []
    (venv, cenv, []) <- abstract [((node, "head"), ty)] x
    (venv', cenv', []) <- abstract [((node, "tail"), tailTy)] xs
    pure (venv ++ venv', cenv ++ cenv', inputs)
  checkPat (_, List _) PNil = pure ([], [], inputs)
  checkPat (src, List ty) (PCons x xs) = do
    node <- next "PCons (List)" Hypo [("head", ty), ("tail", List ty)] []
    (venv, cenv, []) <- abstract [((node, "head"), ty)] x
    (venv', cenv', []) <- abstract [((node, "tail"), List ty)] xs
    pure (venv ++ venv', cenv ++ cenv', inputs)
  checkPat (src, Option ty) (PSome x) = abstract ((src, ty):inputs) x
  checkPat (_, Option _) PNone = pure ([], [], inputs)
  checkPat (_, ty) pat = do
    fc <- req AskFC
    let msg = "Couldn't resolve pattern " ++ show pat ++ " with type " ++ show ty
    req $ Throw $ Err (Just fc) Nothing $ PattErr msg
abstract _ x = err $ "Can't abstract " ++ show x

kabstract :: [(Src, SType Term)]
          -> Abstractor
          -> Checking (KEnv -- Local env for checking body of lambda
                      ,[(Src, SType Term)] -- rightovers
                      )
kabstract [] (Bind x) = fail $ "abstractor: no wires available to bind to " ++ show x
kabstract _ (AThunk _) = fail $ "Can't match kernel thunks"
kabstract (input@(_, ty):inputs) (Bind x)
  = let q = if copyable ty then Tons else One
    in  pure ([(x, (q, input))], inputs)
kabstract inputs (x :||: y) = do
  (kenv, inputs)  <- kabstract inputs x
  (kenv', inputs) <- kabstract inputs y
  pure (kenv ++ kenv', inputs)
kabstract inputs (APull ports abst) = do
  inputs <- pullPorts ports inputs
  kabstract inputs abst
kabstract ((_, Bit):inputs) (Lit (Bool b)) = simpleCheck Boolean (Bool b) $> ([], inputs)
kabstract _ (Lit lit) = err $ "Can't match literal " ++ show lit ++ " in a kernel"
kabstract ((_, Of ty n):inputs) (VecLit xs) = do
  node <- next "natHypo" Hypo [] [("value", SimpleTy Natural)]
  check' n ((), [((node, "value"), SimpleTy Natural)])
  n <- evalNat n
  unless (n == length xs)
    (fail $ "length mismatch in vector pattern")
  venvs <- mapM (aux node) xs
  pure $ (concat venvs, inputs)
   where
    aux node elem = do
      (venv, []) <- kabstract [((node, "type"), ty)] elem
      pure venv
kabstract (input:inputs) (Pat pat) = checkPat input pat
 where
  checkPat :: (Src, SType Term) -> Pattern Abstractor -> Checking (KEnv, [(Src, SType Term)])
  checkPat (_, Of _ n) PNil = evalNatSoft n >>= \case
    Right n -> if n == 0
               then pure ([], inputs)
               else err "Vector length isn't 0 for pattern `Nil`"
    -- If we can't work out what the size is, it might be 0
    Left _  -> pure ([], inputs)
  checkPat (_, Of ty n) (PCons x xs) = do
    n <- evalNat n
    let tailTy = Of ty (Simple (Num (n - 1)))
    node <- knext "PCons" Hypo [("head", ty), ("tail", tailTy)] []
    (venv, []) <- kabstract [((node, "head"), ty)] x
    (venv', []) <- kabstract [((node, "tail"), tailTy)] xs
    pure (venv ++ venv', inputs)
  checkPat (_, ty) pat = do
    fc <- req AskFC
    let msg = "Couldn't resolve pattern " ++ show pat ++ " with type " ++ show ty
    req $ Throw $ Err (Just fc) Nothing $ PattErr msg

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

pp :: Show a => (a, Graph) -> String
pp (outputs, (nodes, wires))
  = unlines $ concat ["nodes:":(show<$>nodes)
                     ,"wires:":(show <$> wires)
                     ,"outputs:":[show outputs]
                     ]

run :: (CEnv, VEnv, [NDecl], [VDecl], FC)
    -> Checking a
    -> Either Error (a, ([TypedHole], Graph))
run (ce, ve, nd, vd, fc) m = let ctx = Ctx { cenv = ce
                                           , venv = ve
                                           , ndecls = nd
                                           , vdecls = vd
                                           , typeFC = fc
                                           , stack = []
                                           } in
                               runBarf $ (\(a,b,_) -> (a,b)) <$> handler m ctx root


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
  (outs,  ([], rightunders)) <- kcheck t (overs, unders)
  pure (outs, (rightovers, rightunders))
kcheck' (binder :\: body) (overs, unders) = do
  (ext, overs) <- kabstract overs (unWC binder)
  (outs, ((), unders)) <- localKVar ext $ kcheck body ((), unders) <* req KDone
  pure (outs, (overs, unders))
kcheck' (Pull ports t) (overs, unders) = do
  unders <- pullPorts ports unders
  kcheck t (overs, unders)
{-
kcheck'  (t ::: outs) (overs, ())= do
  (unders, dangling) <- mkIds outs
  ((), (overs, [])) <- kcheck t (overs, unders)
  pure (dangling, (overs, ()))
 where
  mkIds :: [Output] -> Checking ([(Tgt, SType)] -- Hungry wires
                                ,[(Src, SType)]) -- Dangling wires
  mkIds [] = pure ([], [])
  mkIds ((port, ty):outs) = do
    node <- next "id" Id [(port, ty)] [(port, ty)]
    (hungry, dangling) <- mkIds outs
    pure (((node, port), ty):hungry, ((node, port), ty):dangling)
-}
kcheck' (Emb t) (overs, unders) = do
  (outs, (overs, ())) <- kcheck t (overs, ())
  unders <- kcheckOutputs unders outs
  pure ((), (overs, unders))
 where
  kcheckOutputs :: [(Tgt, SType Term)] -> [(Src, SType Term)] -> Checking [(Tgt, SType Term)]
  kcheckOutputs tys [] = pure tys
  kcheckOutputs ((tgt, ty):tys) ((src, ty'):outs)
   | ty == ty' = wire (src, Left ty, tgt) *> kcheckOutputs tys outs
  kcheckOutputs _ _ = fail "check (kernel): checkOutputs failed"
kcheck' (Th _) _ = fail "no higher order signals! (Th)"
kcheck' (Var x) ((), ()) = do
  output <- req $ KLup x
  pure ([output], ((), ()))
kcheck' (Do x) (overs, ()) | (n :|: n') <- unWC x = do
  let lfc = fcOf n
  let rfc = fcOf n'
  kcheck' ((WC lfc (Do n)) :|: (WC rfc (Do n'))) (overs, ())
kcheck' (Do t) (overs, ()) = do
  ([(src, K (R ss) (R ts))], ((), ())) <- check t ((), ())
  this <- knext "eval" (Eval src) ss ts
  overs <- ksolder this overs ss
  pure ([ ((this, port), ty) | (port, ty) <- ts], (overs, ()))
-- TODO: find a way to make check perceive this as a function
-- Check brat functions and arguments assuming they'll produce a kernel
kcheck' (fun :$: arg) ((), ())
   | Var f <- unWC fun = do
      -- traceM $ "Looking for " ++ show f
      mv <- req $ VLup f
      case mv of
        Just (src, (K (R ss) (R ts))) -> trace "kernel" $ kernel f ss ts
        Nothing -> trace "function" $ req (CLup f) >>= \case
          Just (ss :-> ts) -> function f ss ts
          Nothing -> req AskFC >>= \fc -> req $ Throw $ Err (Just fc) Nothing $ VarNotFound f

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
                     _ -> err "BRAT function called from kernel"
  evalNode <- knext "eval" (Eval src) ss ts
  ((), ((), [])) <- kcheck arg ((), [((evalNode, port), ty) | (port, ty) <- ss])
  pure ([ ((evalNode, port), ty) | (port, ty) <- ts], ((), ()))
   where
     function f ss ts = do
      funNode  <- next ("prim_" ++ f) (Prim f) ss ts
      argResult <- check arg ((), [ ((funNode, port), ty) | (port, ty) <- ss ])
      let ((), ((), [])) = argResult
      let tys = [ ((funNode, port), ty) | (port, ty) <- ts ]
      (src, ss, ts) <- case tys of
                         [(src, K (R ss) (R ts)), (_, K (R us) (R vs))] -> pure (src, (ss <> us), (ts <> vs))
                         ((src, K (R ss) (R ts)):_) -> pure (src, ss, ts)
                         _ -> err "BRAT function called from kernel"
      evalNode <- knext "eval" (Eval src) ss ts
      ((), ((), [])) <- kcheck arg ((), [((evalNode, port), ty) | (port, ty) <- ss])
      pure ([ ((evalNode, port), ty) | (port, ty) <- ts], ((), ()))


     kernel f ss ts = do
      funNode  <- knext ("prim_" ++ f) (Prim f) ss ts
      argResult <- kcheck arg ((), [ ((funNode, port), ty) | (port, ty) <- ss ])
      let ((), ((), [])) = argResult
      let tys = [ ((funNode, port), ty) | (port, ty) <- ts ]
      pure (tys, ((), ()))

kcheck' (NHole name) ((), unders) = do
  fc <- req AskFC
  req $ LogHole $ NKHole name fc ((), unders)
  pure ((), ((), []))
kcheck' (VHole name) (overs, unders) = do
  fc <- req AskFC
  req $ LogHole $ VKHole name fc (overs, unders)
  pure ((), ([], []))
kcheck' (Vec elems) ((), (_, Of ty n):unders) = do
  hypo <- next "nat hypo" Hypo [] []
  fc   <- req AskFC
  check1 ((hypo, "ty"), SimpleTy Natural) (WC fc n)

  hypo <- next "vec type hypo" Hypo [] []
  mapM_ (aux [((hypo, "ty"), ty)]) elems

  ceval n >>= \case
    Left (Err _ src msg) -> req AskFC >>= \fc -> req (Throw $ Err (Just fc) src msg)
    Right (VSimple (Num n)) -> if length elems == n
                               then pure ((), ((), unders))
                               else fail $ unwords ["Vector is length"
                                                   ,show (length elems)
                                                   ,"but it should be length"
                                                   ,show n
                                                   ]
    Right v -> fail $ unwords ["Trying to reduce", show n, "but got", show v]
 where
  aux ty tm = do ((), ((), [])) <- kcheck tm ((), ty)
                 pure ()
kcheck' (Simple (Bool _)) ((), ((_, Bit):unders)) = pure ((), ((), unders))
kcheck' t _ = fail $ "Won't kcheck " ++ show t

