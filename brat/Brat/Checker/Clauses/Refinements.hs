{-# LANGUAGE FlexibleContexts #-}

module Brat.Checker.Clauses.Refinements where

import Brat.Error
import Brat.Graph (Thing(..))
import Brat.Syntax.Abstractor
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.Checker.Helpers
import Brat.Checker.Helpers.Nodes
import Brat.Checker.Monad
import Brat.Checker.Types (ValueType)
import Brat.UserName
import Bwd

import Data.Functor ((<&>), ($>))

type Subst = [(String, Src)] -- Pattern variables which stand for sources

type PatRefinement = Pattern -> Checking (Maybe (Subst, NormalisedAbstractor))
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
 -> Checking (Maybe (Subst
                    , NormalisedAbstractor
                    ,[(PortName, BinderType m)]   -- Overs
                    ,[(PortName, BinderType m)])) -- Unders

-- Combine independent pattern and type refinements
ref :: Modey m -> PatRefinement -> TypeRefinement m -> Refinement m
ref _m patRef typeRef pat ends over overs unders = do
  (overs,unders) <- typeRef ends over overs unders
  patRef pat <&> \case
    Just (sg, na) -> Just (sg, na, overs, unders)
    Nothing -> Nothing

refinementZero :: BinderType Brat -> Refinement Brat
refinementZero ty = ref Braty (patRefinementZero ty) (typeRefinementZero ty)
 where
  patRefinementZero :: BinderType Brat -> PatRefinement
  patRefinementZero _ DontCare = pure $ Just ([], NA (APat DontCare))
  patRefinementZero _ (Lit (Num 0)) = pure (Just ([], NA (APat DontCare)))
  patRefinementZero _ PZero = pure (Just ([], NA (APat DontCare)))
  patRefinementZero ty (Bind x) = do
   const0 <- constNode Braty ty (Num 0)
   case ty of
     Left Nat -> defineSrc const0 (VNum nZero)
     _ -> pure ()
   pure $ Just ([(x, const0)], NA (APat DontCare))
  -- doub(0) = 0, so keep going
  patRefinementZero _ (PTwoTimes n) = pure $ Just ([], NA (APat n))
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
  (overs :-> unders) <- case ty of
    Left Nat -> defineSrc nPlus1 (VNum (nPlus 1 (nVar (VPar (ExEnd (end n)))))) $>
                (changeVars (InxToPar (ends :< ExEnd (end nPlus1))) 0 (doesItBind Braty) $
                (overs :-> unders))
    _ -> pure (overs :-> unders)
  stuff <- case pat of
    DontCare -> pure $ Just ([], NA (APat DontCare))
    Bind x -> pure $ Just ([(x,nPlus1)], NA (APat DontCare))
    POnePlus p -> pure $ Just ([], NA (APat p))
    _ -> pure Nothing
  pure $ (\(sg, abs) -> (sg, abs, (p,ty):overs, unders)) <$> stuff

refinementNil :: Modey m -> Refinement m
refinementNil m pat ends (p,ty) overs unders = ref m (patRefinementNil m ty) (refineType m) pat ends (p,ty) overs unders
 where
  patRefinementNil :: Modey m -> BinderType m -> PatRefinement
  patRefinementNil _ _ DontCare = pure $ Just ([], NA $ APat DontCare)
  patRefinementNil _ _ PNil = pure $ Just ([], NA $ APat DontCare)
  patRefinementNil Kerny (Of elTy _n) (Bind x) = do
    (_,_,[(nil,_)],_) <- knext "" (Constructor (plain "nil")) (B0,B0) [] [("value", Of elTy (VNum nZero))]
    pure $ Just ([(x, nil)], NA $ APat DontCare)
  patRefinementNil Braty (Right ty) (Bind x) | Just (elTy, _n) <- getVec Braty ty = do
    (_,_,[(nil,_)],_) <- next "" (Constructor (plain "nil")) (B0,B0) [] [("value", Right (TVec elTy (VNum nZero)))]
    pure $ Just ([(x, nil)], NA $ APat DontCare)
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
refinementCons m = ref m patRefinementCons (typeRefinementCons m)
 where
  patRefinementCons :: PatRefinement
  patRefinementCons DontCare = pure $ Just ([], NA $ APat DontCare :||: (APat DontCare :||: APat DontCare))
  patRefinementCons (PCon (PrefixName [] "cons") abs) = pure $ Just ([], normaliseAbstractor (APat DontCare :||: abs))
  patRefinementCons (Bind x) = pure $ Just ([], NA (APat (Bind x) :||: (APat DontCare :||: APat DontCare)))
  patRefinementCons _ = pure Nothing

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
    ty' <- evBi m (changeVar (InxToPar ends) 0 ty)
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
    = fmap (\(sg,a) -> (sg,a,(p,ty):overs,unders)) <$> case pat of
    Bind x -> do
      bool <- constNode m ty (Bool b)
      pure (Just ([(x, bool)], NA (APat DontCare)))
    DontCare -> pure (Just ([], NA (APat DontCare)))
    Lit (Bool b') -> pure $ if b == b'
                            then (Just ([], NA (APat DontCare)))
                            else Nothing
    _ -> pure Nothing

refinementNone :: Refinement Brat
refinementNone pat _ (p,ty) overs unders
  = fmap (\(sg,abs) -> (sg,abs,(p,ty):overs,unders)) <$> case pat of
  DontCare -> pure (Just ([], NA (APat DontCare)))
  PNone -> pure (Just ([], NA (APat DontCare)))
  Bind x -> do
    (_, [], [(value,_)], _) <- next "" (Constructor (plain "none")) (B0,B0)
                               [] [("value", ty)]
    pure (Just ([(x, value)], NA (APat DontCare)))
  _ -> pure Nothing


-- Like with cons, add the unpacked thing after the Option
-- `Option(X)` becomes `Option(X), X`
-- `some(x)`   becomes `_, x`
refinementSome :: Refinement Brat
refinementSome pat _ o@(p,Right (TOption ty)) overs unders
  = let overs' = o:(p++".value",Right ty):overs in
  fmap (\(sg,abs) -> (sg,abs,overs',unders)) <$>
    case pat of
      DontCare -> pure (Just ([], NA (APat DontCare :||: APat DontCare)))
      PSome p -> pure (Just ([]
                            ,normaliseAbstractor (APat DontCare
                                                  :||: APat p)))
      Bind x -> pure (Just ([]
                           ,NA (APat (Bind x) :||: APat DontCare)))
      _ -> pure Nothing

refinementExactly :: SimpleTerm -> Refinement Brat
refinementExactly tm pat _ (p,ty) overs unders
  = fmap (\(sg,abs) -> (sg,abs,(p,ty):overs,unders)) <$> case pat of
  Bind x -> do
    tm <- constNode Braty ty tm
    pure (Just ([(x,tm)], NA (APat DontCare)))
  DontCare -> pure (Just ([], NA (APat DontCare)))
  Lit tm' | tm == tm' -> pure (Just ([], NA (APat DontCare)))
  _ -> pure Nothing

-- The opposite of refinementExactly
refinementNot :: SimpleTerm -> Refinement Brat
refinementNot tm pat _ (p,ty) overs unders
  = fmap (\(sg,abs) -> (sg,abs,(p,ty):overs,unders)) <$> case pat of
  Bind _ -> pure (Just ([], NA (APat pat)))
  DontCare -> pure (Just ([], NA (APat pat)))
  Lit tm' | tm /= tm' -> pure (Just ([], NA (APat pat)))
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
    (overs :-> unders) <- case ty of
      Left Nat -> defineSrc nTimes2 (VNum (n2PowTimes 1 (nVar (VPar (ExEnd (end n)))))) $>
                  changeVars (InxToPar (ends :< ExEnd (end nTimes2))) 0 (doesItBind Braty) (overs :-> unders)
      _ -> pure (overs :-> unders)
    pure (Just (maybe [] (\x -> [(x,nTimes2)]) msg, na, (p,ty):overs, unders))

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
  (overs :-> unders) <- case ty of
    Left Nat -> pure $ changeVars (InxToPar (ends :< nEnd)) 0 (doesItBind Braty) (overs :-> unders)
    _ -> pure $ overs :-> unders
  pure . fmap (\(sg,abs) -> (sg,abs,(p,ty):overs,unders)) $ case pat of
    DontCare -> Just ([], NA (APat DontCare))
    Bind x -> Just ([(x,n)], NA (APat DontCare))
    POnePlus (PTwoTimes p) -> patRefinementEven p <&> \(msg,p) -> (maybe [] (\x -> [(x,nPred)]) msg, p)
    _ -> Nothing
