{-# LANGUAGE
AllowAmbiguousTypes,
FlexibleContexts,
MultiParamTypeClasses,
ScopedTypeVariables,
UndecidableInstances
#-}

module Brat.Checker.Clauses (checkBody) where

import Brat.Checker
import Brat.Checker.Clauses.Refinements
import Brat.Checker.Helpers
import Brat.Checker.Monad (err, throwLeft, localEnv)
import Brat.Checker.Types
import Brat.Error
import Brat.Eval
import Brat.FC hiding (end)
import qualified Brat.FC as FC
import Brat.Graph (Thing(Hypo))
import Brat.Syntax.Abstractor
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Control.Monad.Freer (req)
import Util (nth)

import Control.Arrow ((&&&))
import Control.Monad.Writer
import Data.Functor ((<&>))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import qualified Data.Set as S

{-
The process for checking definitions with multiple clauses (as is done by checkClauses):
  * Turn each of the clauses into a Branch, with mkBranch
  * Create some overs and unders to check against, given the signature of the function
  * Pass these connectors and a list of branches into Build, to create the box and do the checking

Build then does the following:
  * Check if the first branch doesn't discriminate - if it doesn't, we can ignore the rest of the branches
  * Otherwise, the function `isIndiscriminate` returns a test to do and an index from the overs to do it on
  * Perform the given test by calling `doTest` (TODO)
  * Create boxes for the continuations
  * Build selections into those boxes, extracting the relevant into for each possible result of the test (possibilities) (TODO)
  * Partition our remaining list of branches into the ones which are still possible after each test result
  * Recursively call on our new boxes, connectors, and list of branches
  * Check that all branches have been reached, and emit an error if not
-}

data Branch m = Branch
  { index :: Int  -- Which clause is this (in the order they're defined in source)
  , body :: WC (Term Chk Noun) -- The RHS of the clause
  , lhsFC :: FC -- File context of the LHS of the clause
  -- Everything else gets refined as we go
  , case_ :: Case m
  , subst :: Subst m
  }
deriving instance (Show (BinderType m), Show (EnvData m)) => Show (Branch m)

clauseFC :: Branch m -> FC
clauseFC Branch{..} = FC (FC.start lhsFC) (FC.end $ fcOf body)

data Test
  = Zero0Succ1
  | Nil0Cons1
  | False0True1
  | None0Some1
  | Not0Exactly1 SimpleTerm
  | Odd0Even1
 deriving Show

data Pair a = a :& a

data TypeOrKind = ToKType | ToKKind
instance Show TypeOrKind where
  show ToKType = "type"
  show ToKKind = "kind"

data PatResult m
 = Indiscriminate
 | Discriminate (Test, Bool)
 | Invalid TypeOrKind (ValueType m)

type PortTest = (Int, Test)

-- This is the entry point to checking the body of a function, called by `Load`
checkBody :: (?my :: Modey m, CheckConstraints m UVerb, Eval (BinderType m))
             => String
             -> FunBody Term UVerb
             -> (FunVal m)
             -> Checking Src
checkBody _ Undefined _ = err (InternalError "Checking undefined clause")
checkBody name (NoLhs verb) (FV ctx ss ts) = checkThunk name ctx ss ts verb
checkBody name (Clauses cs) fv@(FV ctx ss ts) = do
  let bs = uncurry (mkBranch fv) <$> (NE.zip (NE.fromList [0..]) cs)
  -- The box that contains all the branches for the function
  (box, usedBranches) <- makeBox name ctx ss ts $
    -- Do graph building, typechecking, and get back a list of every clause reached
    \(overs, unders) -> snd <$> runWriterT (build name overs bs unders)
  checkAllBranchesReached usedBranches bs
  pure (fst box)
 where
  checkAllBranchesReached reachedBranches bs = do
    let allBranches = S.fromList (NE.toList (index <$> bs))
    -- S.difference finds elements of the first set that aren't in the second
    let unusedBranches = S.difference allBranches reachedBranches
    unless (S.null unusedBranches) $ do
      let b = head (S.toList unusedBranches)
      let branch = head (NE.filter ((== b) . index) bs)
      localFC (clauseFC branch) $ err UnreachableBranch

-- Turn the constituent parts of a clause into a branch,
-- so that it can be refined and "built"
mkBranch :: FunVal m
         -> Int
         -> (WC Abstractor, WC (Term Chk Noun)) -- The clause that we're making a branch for
         -> Branch m
mkBranch (FV B0 ss ts) i (WC absFC abs, tm)
  = Branch
    { index = i
    , body  = tm
    , lhsFC = absFC
    , case_ = Case { lhs = normaliseAbstractor abs, covers = ss, cunders = ts }
    , subst = []
    }

build :: forall m. (?my :: Modey m, CheckConstraints m UVerb, Eval (BinderType m))
      => String              -- Name of the function we're building
      -> Overs m UVerb       -- Gamma (All overs to the graph)
      -> NonEmpty (Branch m) -- Our potential branches
      -> Unders m Chk        -- Delta (All unders from the graph)
      -- Return a Src which emits the outermost box, and collect a set of branches
      -- which have been reached in the Writer monad
      -> WriterT (S.Set Int) Checking ()
build name overs (b :| branches) unders = do
  (pats, overs) <- lift $ absList (lhs (case_ b)) overs
  lift (localFC (clauseFC b) $ areIndiscriminate (0,B0) overs pats) >>= \case
    -- If the first branch doesn't discriminate, we can wire it up directly
    -- Start by announcing that we've reached this branch
    Right _ -> tell (S.singleton (index b)) *> lift (do
      let tm = WC (lhsFC b) (unNA . lhs . case_ $ b) :\: body b
      let env = M.fromList $ (\(x,over) -> (plain x, over)) <$> (subst b)
      ((), emptyOvers) <- localFC (clauseFC b) $
                          noUnders $
                          localEnv env $
                          check (WC (clauseFC b) tm) (overs, unders)
      ensureEmpty "build leftovers" emptyOvers
      )
    Left (i, test) -> do
      (fRef :& tRef) <- lift $ throwLeft $ possibilities (i, test) (rowToSig overs)

      buildOrDont (b:|branches) (fRef, i) False (covers $ case_ b) (cunders $ case_ b)
      buildOrDont (b:|branches) (tRef, i) True  (covers $ case_ b) (cunders $ case_ b)

      pure ()
 where
  absList :: NormalisedAbstractor -> [(Src, BinderType m)] -> Checking ([Pattern], [(Src, BinderType m)])
  absList na overs = absListWorker na overs <&> \(pats, lovers, rovers) -> (pats, lovers ++ rovers)
   where
    absListWorker :: NormalisedAbstractor -> [(Src, BinderType m)] -> Checking ([Pattern], [(Src, BinderType m)], [(Src, BinderType m)])
    absListWorker (NA abs) overs = case abs of
      AEmpty -> pure ([], [], overs)
      a :||: b -> do
        (as, lovers, rovers) <- absListWorker (normaliseAbstractor a) overs
        (bs, lovers', rovers') <- absListWorker (normaliseAbstractor b) rovers
        pure (as ++ bs, lovers ++ lovers', rovers')
      APull ps abs -> pullPortsRow ps overs >>= absListWorker (normaliseAbstractor abs)
      APat p -> case overs of
        [] -> err $ NothingToBind (show p)
        (o:os) -> pure ([p], [o], os)

  buildOrDont :: NonEmpty (Branch m)
              -> (Refinement m, Int)
              -> Bool -- Branch type
              -> [(PortName, BinderType m)] -- Overs
              -> [(PortName, BinderType m)] -- Unders
              -> WriterT (S.Set Int) Checking Src
  buildOrDont bs (ref, i) whichCase overs unders = do
    ((dangling, _), reached) <- lift $ do
      -- We return "reached" here rather than using WriterT in order to fit 'makeBox'
      refinedBranches <- catMaybes . NE.toList <$> traverse (refineBranch ref i) bs

      let (ga,de) = getSig refinedBranches overs unders
      makeBox (name ++ "_" ++ show whichCase) B0 ga de $
        \(boxOvers, boxUnders) -> do
          boxUnders <- evalTgtRow ?my boxUnders
          boxOvers  <- evalSrcRow ?my boxOvers
          case refinedBranches of
            [] -> pure S.empty
            -- Ignore the inner thunks for now. We're just type checking branches,
            -- not yet wiring everything up
            (b:bs) -> snd <$> (runWriterT $ build (name ++ "/" ++ show whichCase) boxOvers (b :| bs) boxUnders)
    tell reached
    pure dangling

  getSig [] ga de = (ga,de)
  getSig (b:_) _ _ = (covers &&& cunders) (case_ b)


refineBranch :: forall m. (?my :: Modey m, DeBruijn (BinderType m), Show (BinderType m))
             => Refinement m -> Int -> Branch m -> Checking (Maybe (Branch m))
refineBranch ref i b
  = refine B0 i (case_ b)
  <&> fmap (\(sg, c) -> b { case_ = c
                          , subst = sg
                          })
 where
  -- Navigate to a certain point (given by the Int argument) of an abstractor and
  -- row of overs, then apply a given refinement at that point.
  -- Binders that we pass along the way have ends generated for applying substitutions
  refine :: Bwd End
         -> Int
         -> Case m
         -> Checking (Maybe (Subst m, Case m))
  -- Handle port pulling before anything else! The index that we're refining
  -- assumes that port pulling has already been done
  refine ends n (Case (NA (APull ps abs)) overs unders)
    = pullPortsSig ps overs >>= \overs -> refine ends n (Case (NA abs) overs unders)
  refine ends 0 (Case (NA abs) (over:overs) unders) = do
    result <- case abs of
      APat p -> ref p ends over overs unders
      (APat p :||: as) -> ref p ends over overs unders <&> \case
        Nothing -> Nothing
        Just (sg, (Case (NA abs) overs unders)) -> Just (sg, (Case (normaliseAbstractor (abs :||: as)) overs unders))
      _ -> err $ InternalError "Found unnormalised pattern"
    pure $ flip fmap result $
      \(sg, (Case (NA b) overs unders)) ->
      let (overs' :-> unders') = changeVars (ParToInx ends) 0 (doesItBind ?my) (overs :-> unders)
        in (sg, (Case (NA b) overs' unders'))
  refine ends i (Case (NA (a :||: b)) (over:overs) unders) = do
    ends <- case (?my, doesItBind ?my (snd over)) of
      (Braty, Just k) -> do
        (_, _, [(value, _)], _) <- next "" Hypo (B0,B0) [] [("value", Left k)]
        pure (ends :< ExEnd (end value))
      _ -> pure ends
    rest <- refine ends (i - 1) (Case (NA b) overs unders)
    pure $ reattach a over <$> rest

  reattach a over (sg, (Case (NA b) overs unders)) = (sg, (Case (normaliseAbstractor (a :||: b)) (over:overs) unders))

-- The refinements that we get if a test is performed
possibilities :: (DeBruijn (BinderType m), ?my :: Modey m)
              => PortTest
              -> [(PortName, BinderType m)]
              -> Either ErrorMsg (Pair (Refinement m))
possibilities (i, test) overs = do
  src <- case overs `nth` i of
    Just src -> pure src
    Nothing -> Left $ InternalError "Couldn't find wire to scrutinise"

  -- Return the refinement corresponding to a given test
  pure $ case (?my, snd src, test) of
    (Braty, ty, Zero0Succ1) -> refinementZero ty :& refinementSucc
    (m, _, Nil0Cons1) -> refinementNil m  :&  refinementCons m
    (m, _, False0True1) -> refinementBool m False :& refinementBool m True
    (Braty, _, None0Some1) -> refinementNone :& refinementSome
    (Braty, _, Not0Exactly1 tm) -> refinementNot tm :& refinementExactly tm
    (Braty, _, Odd0Even1) -> refinementOdd :& refinementEven
    (_, _, t) -> error $ "Don't know how to refine " ++ show t

pushIfBinds :: (?my :: Modey m) => Bwd Value -> (Src, BinderType m) -> Bwd Value
pushIfBinds vals (src, ty) = case doesItBind ?my ty of
  Nothing -> vals
  Just k -> vals :< endVal k (ExEnd (end src))

isIndiscriminate :: (?my :: Modey m, Show (ValueType m))
                 => (Int, Bwd Value) -- Which port are we at?, What ends have we passed?
                 -> (Src, BinderType m) -- The overs corresponding to the abstractor
                 -> Pattern             -- The abstractor we're inspecting
                 -> Checking (Either      -- Either the abstractor discriminates:
                              PortTest    -- ... and requires Test on the index Int of the overs
                              (Int, Bwd Value) -- ... else, here's the new context to continue checking with...
                             )
isIndiscriminate (i, vals) (src, ty) pat = patTest ?my ty pat >>= \case
  Discriminate (t, _b) -> pure (Left (i, t))
  Indiscriminate -> let vals' = pushIfBinds vals (src, ty) in
                      pure $ Right (i + 1, vals')
  Invalid sort ty -> err $ PattErr $ unwords ["Couldn't resolve pattern"
                                             ,show pat
                                             ,"with"
                                             ,show sort
                                             ,show ty
                                             ]
 where
  patTest :: Modey m -> BinderType m -> Pattern -> Checking (PatResult m)
  patTest _ _ DontCare = pure Indiscriminate
  patTest _ _ (Bind _) = pure Indiscriminate
  patTest m aty pat = case (m,aty) of
    (Braty, Right vty) -> eval (req . ELup) vals vty <&> \ty -> patTestClassical ToKType ty pat
    (Braty, Left k) -> pure $ patTestClassical ToKKind (kindType k) pat
    (Kerny, ty) -> eval (req . ELup) vals ty <&> \ty -> patTestKernel ty pat

  patTestKernel :: ValueType Kernel -> Pattern -> PatResult Kernel
  patTestKernel Bit (Lit (Bool b)) = Discriminate (False0True1, b)
  patTestKernel (Of _ n) PNil = case valMatch n (VPNum NP0) of
    Right _ -> Indiscriminate
    Left _ -> Discriminate (Nil0Cons1, False)
  patTestKernel (Of _ n) (PCons _ _) = case valMatch n (VPNum (NP1Plus NPVar)) of
    Right _ -> Indiscriminate
    Left _ -> Discriminate (Nil0Cons1, False)
  -- DontCare and Bind are handled by earlier branches of isIndiscriminate
  patTestKernel ty _ = Invalid ToKType ty

  -- TODO: Make this logic less hard-coded
  patTestClassical :: TypeOrKind -- Is the type secretly a kind?
                   -> ValueType Brat -> Pattern -> PatResult Brat
  patTestClassical _ TInt (POnePlus _) = Indiscriminate
  patTestClassical _ TNat (POnePlus x) = Discriminate $ yankTwoTimes (normaliseAbstractor (APat x))
   where
    yankTwoTimes :: NormalisedAbstractor -> (Test, Bool)
    yankTwoTimes (NA (APat (PTwoTimes _))) = (Odd0Even1, False)
    yankTwoTimes (NA (APat (POnePlus x)))
      = yankTwoTimes (normaliseAbstractor (APat x))
    yankTwoTimes _ = (Zero0Succ1, True)

  patTestClassical _ ty (PTwoTimes _) | isNum ty = Discriminate (Odd0Even1, True)
  patTestClassical _ ty PZero | isNum ty = Discriminate (Zero0Succ1, False)
  patTestClassical _ ty (Lit (Num 0)) | isNum ty = Discriminate (Zero0Succ1, False)
  patTestClassical is ty PNil = case ty of
    TList _ -> Discriminate (Nil0Cons1, False)
    TVec _ n -> case valMatch n (VPNum NP0) of
      Left _ -> Discriminate (Nil0Cons1, False)
      Right _ -> Indiscriminate
    TUnit -> Indiscriminate
    _ -> Invalid is ty
  -- Cons can't be irrefutable for lists because we don't have enough
  -- information to say whether an arbitrary list is nil or not
  patTestClassical _ (TList _) (PCons _ _) = Discriminate (Nil0Cons1, True)
  patTestClassical _ ty (PCon (PrefixName [] "cons") _) | isConsy ty = case uncons Braty ty of
    Just _ -> Indiscriminate
    Nothing -> Discriminate (Nil0Cons1, True)
  patTestClassical _ ty (PCons _ _) | isConsy ty = case uncons Braty ty of
    Just _ -> Indiscriminate
    Nothing -> Discriminate (Nil0Cons1, True)
  patTestClassical is ty PNone = case ty of
    TOption _ -> Discriminate (None0Some1, False)
    _ -> Invalid is ty
  patTestClassical is ty (PSome _) = case ty of
    TOption _ -> Discriminate (None0Some1, True)
    _ -> Invalid is ty
  patTestClassical _ TBool (Lit (Bool b)) = Discriminate (False0True1, b)
  patTestClassical _ ty (Lit tm) | validTm tm ty = Discriminate (Not0Exactly1 tm, True)
  patTestClassical is ty _ = Invalid is ty

  isNum TNat = True
  isNum TInt = True
  isNum _ = False

  isConsy (TList _) = True
  isConsy (TVec _ _) = True
  isConsy (TCons _ _) = True
  isConsy _ = False

  validTm :: SimpleTerm -> ValueType Brat -> Bool
  validTm (Bool _) TBool = error "This should be unreachable"
  validTm (Num _) ty = isNum ty
  validTm (Text _) TText = True
  validTm (Float _) TFloat = True
  validTm _ _ = False

-- Extends `isIndiscriminate` to a list of patterns
-- N.B. if remaining overs are returned, we don't complain here - it
-- will instead be caught when `check` is called on the problematic branch
areIndiscriminate :: (?my :: Modey m, Show (ValueType m))
                 => (Int, Bwd Value) -- Which port are we at?, What ends have we passed?
                 -> [(Src, BinderType m)] -- The overs corresponding to the abstractor
                 -> [Pattern]             -- The patterns we're inspecting
                 -> Checking (Either      -- Either the abstractor discriminates:
                              PortTest    -- ... and requires Test on the index Int of the overs
                              ((Int, Bwd Value) -- ... else, here's the new context to continue checking with...
                              ,[(Src, BinderType m)]) -- ...and the rest of the overs
                             )
areIndiscriminate ctx overs pats
  = foldM (\acc pat -> case acc of
                         Right (_, []) -> err (NothingToBind (show pat))
                         Right (ctx, over:overs) -> isIndiscriminate ctx over pat <&> \case
                           Right ctx -> Right (ctx, overs)
                           Left test -> Left test
                         Left test -> pure $ Left test)
    (Right (ctx, overs))
    pats
