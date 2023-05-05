{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}

module Brat.Checker.Clauses.Refinements where

import Brat.Checker.Types (EnvData)
import Brat.Error
import Brat.Graph (Thing(..))
import Brat.Syntax.Abstractor
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.Checker.Helpers
import Brat.Checker.Helpers.Nodes
import Brat.Checker.Monad
import Brat.Checker.Quantity
import Brat.Checker.Types (ValueType)
import Brat.UserName
import Bwd

import Data.Bifunctor (second)
import Data.Functor ((<&>), ($>))

data TypeSubst
  {- DefineInType: If we have type such as `Vec(X,n)`, DefineInType specifies
     - A pattern which, when applied (via valMatch) selects some variables
       E.g. `VCon "Vec" [VPVar, VPVar]` would select both X and n
     - A value to assign to each variable selected (or `Nothing` to leave it)
       E.g. `B0 :< Nothing :< VNum nZero` would then define n := 0 and leave X as-is
  -}
  = DefineInType (ValPat, Bwd (Maybe Value))
  | DefineKind Value -- If the type we're expecting is a `Kind`, we can define it directly
  | TypeId -- Or do nothing
  deriving Show

-- Pattern variables which stand for sources
data Subst m = Subst
  { termSub :: [(String, EnvData m)] -- Variables to add when checking the RHS of a branch
  , typeSub :: TypeSubst             -- How to define a type variable at the type we're refining
  }
deriving instance Show (EnvData m) => Show (Subst m)

idSubst :: Subst m
idSubst = tmSubst []

tmSubst :: [(String, EnvData m)] -> Subst m
tmSubst tm = Subst tm TypeId

tySubst :: TypeSubst -> Subst m
tySubst ty = Subst [] ty

type PatRefinement m = Pattern -> Checking (Maybe (Subst m, NormalisedAbstractor))
type TypeRefinement m = Bwd End
                     -> (PortName, BinderType m)
                     -> [(PortName, BinderType m)] -- Overs
                     -> [(PortName, BinderType m)] -- Unders
                     -> Checking ([(PortName, BinderType m)] -- Overs
                                 ,[(PortName, BinderType m)] -- Unders
                                 )

-- In order to use a refinement, a function needs to "dig" to the point in both
-- the abstractor and the overs where the test is performed. For example:
-- If we have the function
-- `f(X :: *, n :: #, Vec(X, n)) -> Vec(X,n)`
-- `f(x, succ(n), xs) = _`
-- a refinement `r` should be called like
-- `r 1 (succ(n)) (n :: #, Vec(X, n)) (Vec(X,n))`
type Refinement m
  = Pattern -- The pattern that resulted in us calling this refinement
 -> Bwd End -- A list of ends that we've passed to get to this point in the row
            --  (for doing substitutions)
 -> (PortName, BinderType m) -- input that matches the pattern we're refining
 -> [(PortName, BinderType m)] -- The rest of the inputs after the current one
 -> [(PortName, BinderType m)] -- The outputs from the function
 -> Checking (Maybe (Subst m, Case m))

data Case m = Case
  { lhs :: NormalisedAbstractor       -- LHS
  , covers :: [(PortName, BinderType m)] -- Overs
  , cunders :: [(PortName, BinderType m)] -- Unders
  }

deriving instance Show (BinderType m) => Show (Case m)

-- Combine independent pattern and type refinements
ref :: Modey m -> PatRefinement m -> TypeRefinement m -> Refinement m
ref _m patRef typeRef pat ends over overs unders = do
  (overs,unders) <- typeRef ends over overs unders
  patRef pat <&> \case
    Just (sg, na) -> Just (sg, Case na overs unders)
    Nothing -> Nothing

quantize :: Modey m -> (Src, BinderType m) -> EnvData m
quantize Braty = (:[])
quantize Kerny = (One,)

refinementZero :: BinderType Brat -> Refinement Brat
refinementZero ty = ref Braty (patRefinementZero ty) (typeRefinementZero ty)
 where
  patRefinementZero :: BinderType Brat -> PatRefinement Brat
  patRefinementZero _ DontCare = pure $ Just (idSubst, NA (APat DontCare))
  patRefinementZero _ (Lit (Num 0)) = pure (Just (idSubst, NA (APat DontCare)))
  patRefinementZero _ PZero = pure (Just (idSubst, NA (APat DontCare)))
  patRefinementZero ty (Bind x) = do
   const0 <- constNode Braty ty (Num 0)
   case ty of
     Left Nat -> defineSrc const0 (VNum nZero)
     _ -> pure ()
   pure $ Just (tmSubst [(x, [(const0, ty)])], NA $ APat DontCare)
  -- doub(0) = 0, so keep going
  patRefinementZero _ (PTwoTimes n) = pure $ Just (idSubst, NA (APat n))
  patRefinementZero _ _ = pure Nothing

  typeRefinementZero :: BinderType Brat -> TypeRefinement Brat
  -- If we're refining a Nat kind, instantiate the rest of the signature with 0
  typeRefinementZero ty@(Left Nat) ends over overs unders = do
    zero <- constNode Braty ty (Num 0)
    defineSrc zero (VNum nZero)
    let var = ExEnd (end zero)
    let (overs' :-> unders') = changeVars (InxToPar (ends :< var)) 0 (doesItBind Braty) (overs :-> unders)
    pure (over:overs', unders')
  typeRefinementZero _ _ over overs unders = pure (over:overs,unders)

refinementSucc :: Refinement Brat
refinementSucc pat ends (p,ty) overs unders = do
  -- For the sake of type checking, create two hypothetical ends, with one
  -- defined as (+ 1) of the other. So that when we call `valMatch` on the
  -- index, it'll be recognised as a `succ`essor
  (_, [], [(n,_),(nPlus1,_)],_) <- next "" Hypo (B0,B0) [] [("value", ty),("value", ty)]
  (tySub, overs :-> unders) <- case ty of
    Left Nat -> defineSrc nPlus1 (VNum (nPlus 1 (nVar (VPar (ExEnd (end n)))))) $>
                ((DefineKind (endVal Nat (ExEnd (end n))),) $
                (changeVars (InxToPar (ends :< ExEnd (end nPlus1))) 0 (doesItBind Braty) $
                overs :-> unders))
    _ -> pure (TypeId, overs :-> unders)
  refinedPat <- pure $ case pat of
    Bind x -> Just (Subst [(x,[(nPlus1,ty)])] tySub, NA (APat DontCare))
    _ -> (tySubst tySub,) <$> refinePat pat
  pure $ (\(sg, na) -> (sg, (Case na ((p,ty):overs) unders))) <$> refinedPat
 where
  refinePat :: Pattern -> Maybe NormalisedAbstractor
  refinePat = \case
    DontCare -> Just (NA (APat DontCare))
    POnePlus p -> Just (NA (APat p))
    -- 2*n-1 = 1 + 2*(n - 1)
    PTwoTimes p -> case p of
      Bind x -> Just (NA (APat (POnePlus (PTwoTimes (Bind x)))))
      p -> refinePat p <&> \(NA (APat pat)) -> (NA (APat (POnePlus (PTwoTimes pat))))
    _ -> Nothing

refinementNil :: Modey m -> Refinement m
refinementNil m pat ends (p,ty) overs unders = ref m (patRefinementNil m ty) (refineType m) pat ends (p,ty) overs unders
 where
  patRefinementNil :: Modey m -> BinderType m -> PatRefinement m
  patRefinementNil _ _ DontCare = pure $ Just (idSubst, NA $ APat DontCare)
  patRefinementNil _ _ PNil = pure $ Just (idSubst, NA $ APat DontCare)
  patRefinementNil Kerny (Of elTy _n) (Bind x) = do
    let refinedTy = Of elTy (VNum nZero)
    (_,_,[nil],_) <- knext "" (Constructor (plain "nil")) (B0,B0) [] [("value", refinedTy)]
    pure $ Just (tmSubst [(x, (One, nil))], NA $ APat DontCare)
  patRefinementNil Braty (Right (TVec elTy _n)) (Bind x) = do
    (_,_,[(n,_),nil],_) <- next "" (Constructor (plain "nil")) (B0,B0) [] [("n", Left Nat),("value", Right (TVec elTy (VNum (nVar (VInx 0)))))]
    defineSrc n (VNum nZero)
    let tySub = (DefineInType (VPCon (plain "Vec") [VPVar, VPNum NPVar], B0 :< Nothing :< Just (endVal Nat (ExEnd (end n)))))
    pure $ Just (Subst [(x, [nil])] tySub, NA (APat DontCare))
  patRefinementNil _ _ _ = pure Nothing

  refineType :: Modey m -> TypeRefinement m
  refineType m ends (p,ty) overs unders = do
    (_, _, [(zero,_)], _) <- next "" Hypo (B0,B0) [] [("value", Left Nat)]
    defineSrc zero (VNum nZero)
    let e0 = ExEnd (end zero)
    let v0 = VApp (VPar e0) B0
    -- If there's a number in the type, set it to 0
    pure $ case (m,ty) of
      (Braty, Right (TVec elTy vLen)) -> let (overs', unders') = defineLength Braty e0 vLen overs unders in
                                           ((p, Right (TVec elTy v0)):overs', unders')
      (Kerny, Of ty vLen) -> let (overs', unders') = defineLength Kerny e0 vLen overs unders in
                               ((p, Of ty v0):overs', unders')
      _ -> ((p,ty):overs, unders)
   where
    -- TODO: Do this as part of the substitution
    defineLength :: DeBruijn (BinderType m) => Modey m
                 -> End -> Value
                 -> [(PortName, BinderType m)] -> [(PortName, BinderType m)]
                 -> ([(PortName, BinderType m)], [(PortName, BinderType m)])
    defineLength m zero (VApp (VPar e) B0) overs unders
      = let (overs' :-> unders') = changeVars (InxToPar (ends :< zero)) 0 (doesItBind m) $
                                   changeVars (ParToInx (ends :< e)) 0 (doesItBind m) $
                                   overs :-> unders
        in  (overs', unders')
    defineLength _ _ _ overs unders = (overs, unders)

-- Add two new elements to the row, the head and the tail
-- The type `List(X)`         becomes `List(X), X, List(X)`
-- The type `Vec(X, succ(n))` becomes `Vec(X, succ(n)), X, Vec(X, n)`
-- The pattern   `cons(x,xs)` becomes `_, x, xs`
refinementCons :: DeBruijn (BinderType m) => Modey m -> Refinement m
refinementCons m = ref m (patRefinementCons m) (typeRefinementCons m)
 where
  patRefinementCons :: Modey m -> PatRefinement m
  patRefinementCons _ DontCare = pure $ Just (idSubst, NA $ APat DontCare :||: (APat DontCare :||: APat DontCare))
  patRefinementCons _ (PCon (PrefixName [] "cons") abs) = pure $ Just (idSubst, normaliseAbstractor (APat DontCare :||: abs))
  patRefinementCons _ (Bind x) = pure $ Just (idSubst, NA (APat (Bind x) :||: (APat DontCare :||: APat DontCare)))
  patRefinementCons _ _ = pure Nothing

  typeRefinementCons :: DeBruijn (BinderType m) => Modey m -> TypeRefinement m
  typeRefinementCons Braty _ (p, ty@(Right (TCons x ys))) overs unders
    = pure $
      ((p,ty)
      :(p++".head", Right x)
      :(p++".tail", Right ys)
      :overs
      ,unders)
  typeRefinementCons m ends (p,ty) overs unders = do
    -- Evaluate ty before inspecting it to see if we can safely uncons it
    -- And substitute because it might have VInx references to things earlier in
    -- the signature (before the point we started refining)
    -- We only inspect this evaluated type (ty') and give back ty instead,
    -- because we want to give back a type with Inx variables
    ty' <- evalBinder m (changeVar (InxToPar ends) 0 ty)
    case uncons m (binderToValue m ty') of
      Just (head, tail) -> pure $
                           ((p,ty)
                           :(p++".head", valueToBinder m head)
                           :(p++".tail", valueToBinder m tail)
                           :overs
                           ,unders
                           )
      -- If uncons fails, either we have a vector (Of or TVec) but don't know
      -- enough about its length argument, or we have something that isn't a list.
      -- In the former case, replace the length with a hypothetical variable
      -- that's defined to be a successor
      Nothing -> case deconstructVec m ty' of
        Just (f, ty, n) -> do
          (_, _, [(x,_),(succX,_)],_) <- next "" Hypo (B0,B0) []
                                         [("x", Left Nat)
                                         ,("succX", Left Nat)]
          defineSrc succX (VNum (nPlus 1 (nVar (VPar (ExEnd (end x))))))
          let replaceEnd e = changeVars (ParToInx (ends :< e)) 0 (doesItBind m) $
                             changeVars (InxToPar (ends :< ExEnd (end succX))) 0 (doesItBind m) $
                             overs :-> unders
          let (overs' :-> unders') = case n of
                VApp (VPar e) B0 -> replaceEnd e
                VNum n
                 | Right (B0 :< (VNum nv)) <- numMatch B0 n NPVar
                 , NumValue 0 (StrictMonoFun (StrictMono 0 (Linear (VPar e)))) <- nv -> replaceEnd e
                _ -> overs :-> unders
          pure $ ((p, valueToBinder m (f ty (endVal Nat (ExEnd (end succX)))))
                  :(p++".head", valueToBinder m ty)
                  :(p++".tail", valueToBinder m (f ty (endVal Nat (ExEnd (end x)))))
                  :overs'
                 ,unders')
        _ -> err $ InternalError "Calling refinement cons on something not list-like"

  deconstructVec :: Modey m -> BinderType m -> Maybe (ValueType m -> ValueType Brat -> ValueType m, ValueType m, ValueType Brat)
  deconstructVec Braty (Right (TVec ty n)) = Just (TVec, ty, n)
  deconstructVec Kerny (Of ty n) = Just (Of, ty, n)
  deconstructVec _ _ = Nothing

refinementBool :: DeBruijn (BinderType m) => Modey m -> Bool -> Refinement m
refinementBool m b = refinement
 where
  refinement pat _ (p,ty) overs unders
    = fmap (\(sg,a) -> (sg,(Case a ((p,ty):overs) unders))) <$> case pat of
    Bind x -> do
      bool <- constNode m ty (Bool b)
      pure (Just (tmSubst [(x, quantize m (bool, ty))], NA (APat DontCare)))
    DontCare -> pure (Just (idSubst, NA (APat DontCare)))
    Lit (Bool b') -> pure $ if b == b'
                            then (Just (idSubst, NA (APat DontCare)))
                            else Nothing
    _ -> pure Nothing

refinementNone :: Refinement Brat
refinementNone pat _ (p,ty) overs unders
  = fmap (\(sg,abs) -> (sg,(Case abs ((p,ty):overs) unders))) <$> case pat of
  DontCare -> pure (Just (idSubst, NA (APat DontCare)))
  PNone -> pure (Just (idSubst, NA (APat DontCare)))
  Bind x -> do
    (_, [], value, _) <- next "" (Constructor (plain "none")) (B0,B0)
                               [] [("value", ty)]
    pure (Just (tmSubst [(x, value)], NA (APat DontCare)))
  _ -> pure Nothing


-- Like with cons, add the unpacked thing after the Option
-- `Option(X)` becomes `Option(X), X`
-- `some(x)`   becomes `_, x`
refinementSome :: Refinement Brat
refinementSome pat _ o@(p,Right (TOption ty)) overs unders
  = let overs' = o:(p++".value",Right ty):overs in
  fmap (\(sg,abs) -> (sg,(Case abs overs' unders))) <$>
    case pat of
      DontCare -> pure (Just (idSubst, NA (APat DontCare :||: APat DontCare)))
      PSome p -> pure (Just (idSubst
                            ,normaliseAbstractor (APat DontCare
                                                  :||: APat p)))
      Bind x -> pure (Just (idSubst
                           ,NA (APat (Bind x) :||: APat DontCare)))
      _ -> pure Nothing

refinementExactly :: SimpleTerm -> Refinement Brat
refinementExactly tm pat _ (p,ty) overs unders
  = fmap (\(sg,abs) -> (sg,(Case abs ((p,ty):overs) unders))) <$> case pat of
  Bind x -> do
    tm <- constNode Braty ty tm
    pure (Just (tmSubst [(x, [(tm,ty)])], NA (APat DontCare)))
  DontCare -> pure (Just (idSubst, NA (APat DontCare)))
  Lit tm' | tm == tm' -> pure (Just (idSubst, NA (APat DontCare)))
  _ -> pure Nothing

-- The opposite of refinementExactly
refinementNot :: SimpleTerm -> Refinement Brat
refinementNot tm pat _ (p,ty) overs unders
  = fmap (\(sg,abs) -> (sg,(Case abs ((p,ty):overs) unders))) <$> case pat of
  Bind _ -> pure (Just (idSubst, NA (APat pat)))
  DontCare -> pure (Just (idSubst, NA (APat pat)))
  Lit tm' | tm /= tm' -> pure (Just (idSubst, NA (APat pat)))
  _ -> pure Nothing

patRefinementEven :: Pattern -> Maybe (Maybe String, NormalisedAbstractor)
patRefinementEven (Bind x) = Just (Just x, NA (APat DontCare))
patRefinementEven DontCare = Just (Nothing, NA (APat DontCare))
patRefinementEven (PTwoTimes p) = Just (Nothing, normaliseAbstractor (APat p))
patRefinementEven (POnePlus (POnePlus (PTwoTimes p))) = Just (Nothing, normaliseAbstractor (APat (POnePlus p)))
patRefinementEven _ = Nothing

-- We're turning `doub(x)` into `x`
-- So refine the type to be (2*) of some end
refinementEven :: Refinement Brat
refinementEven pat ends (p,ty) overs unders = case patRefinementEven pat of
  Nothing -> pure Nothing
  Just (msg, na) -> do
    (_,_,[(n,_), (nTimes2,_)],_) <- next "" Hypo (B0,B0) [] [("n", ty), ("nTimes2", ty)]
    (tySub, overs :-> unders) <- case ty of
      Left Nat -> defineSrc nTimes2 (VNum (n2PowTimes 1 (nVar (VPar (ExEnd (end n)))))) $>
                  (DefineKind (endVal Nat (ExEnd (end n)))
                  ,changeVars (InxToPar (ends :< ExEnd (end nTimes2))) 0 (doesItBind Braty) (overs :-> unders))
      _ -> pure (TypeId, overs :-> unders)
    let subst = case msg of
         Nothing -> tySubst tySub
         (Just x) -> Subst [(x,[(nTimes2,ty)])] tySub
    pure (Just (subst, (Case na ((p,ty):overs) unders)))

-- We're refining the pattern from `1+(2*n)` to `n` (the rounded down half)
-- So we need to change n to 1+(2* some end)
refinementOdd :: Refinement Brat
refinementOdd pat ends (p,ty) overs unders = do
  (_,_,[(fh,_),(nPred,_),(n,_)],_) <- next "" Hypo (B0,B0) []
                                      [("fh", ty),("nPred",ty),("n", ty)]
  case ty of
    Left Nat -> defineSrc nPred (VNum (n2PowTimes 1 (nVar (VPar (ExEnd (end fh)))))) *>
                defineSrc n (VNum (nPlus 1 (nVar (VPar (ExEnd (end nPred))))))
    _ -> pure ()
  let nEnd = ExEnd (end n)
  let (tySub, overs' :-> unders') = case ty of
        Left Nat -> (DefineKind (endVal Nat (ExEnd (end fh)))
                    ,changeVars (InxToPar (ends :< nEnd)) 0 (doesItBind Braty) (overs :-> unders))
        _ -> (TypeId, overs :-> unders)
  let msubst = case pat of
        DontCare -> Just (Subst [] tySub, NA (APat DontCare))
        Bind x -> Just (Subst [(x, [(n,ty)])] tySub, NA (APat DontCare))
        POnePlus (PTwoTimes p) -> patRefinementEven p <&> \(msg,p) -> let tmSub = maybe [] (\x -> [(x,[(nPred, ty)])]) msg in
                                                                               (Subst tmSub tySub, p)
        _ -> Nothing
  pure ((second (\abs -> Case abs ((p,ty):overs') unders')) <$> msubst)
