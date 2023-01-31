module Brat.Syntax.Value (VDecl
                         ,VVar(..)
                         ,NumValue(..)
                         ,Fun00(..)
                         ,StrictMono(..), Monotone(..)
                         ,nZero, nVar, nConstant
                         ,nPlus, n2PowTimes, nFull
                         ,pattern TNat, pattern TInt
                         ,pattern TFloat, pattern TBool
                         ,pattern TText, pattern TOption
                         ,pattern TUnit, pattern TNil, pattern TCons
                         ,pattern TList, pattern TVec
                         ,Value(..),SValue
                         ,BinderType
                         ,ValPat(..), valMatch, valMatches
                         ,NumPat(..), numMatch
                         ,DeBruijn(..), VarChanger(..), changeVars
                         ,doesItBind, doesItBind2
                         ,endVal, varVal
                         ) where

import Brat.Error
import Brat.Syntax.Common
import Brat.Syntax.Core (Term (..))
import Brat.UserName
import Bwd

import Data.List (intercalate, minimumBy)
import Data.Ord (comparing)
import Control.Monad.State
import Control.Arrow (Arrow(second))
import Data.Maybe (isJust)

type VDecl = Decl' (PortName, KindOr Value) (FunBody Term Noun)

data VVar {- n -} -- Under n de Bruijn indices
 = VPar End -- Has to be declared in the Store (for equality testing)
 | VInx Int -- Has to be < n
 | VLvl Int TypeKind -- Cache the kind for equality testing
 deriving (Eq, Show)

data NumValue = NumValue
  { upshift :: Int
  , grower  :: Fun00
  } deriving Eq

instance Show NumValue where
  show (NumValue 0 g) = show g
  show (NumValue n Constant0) = show n
  show (NumValue n g) = show n ++ " + " ++ show g

-- Functions which map 0 to 0
data Fun00
 = Constant0
 | StrictMonoFun StrictMono
 deriving Eq

instance Show Fun00 where
  show Constant0 = "0"
  show (StrictMonoFun sm) = show sm

-- Strictly increasing function
data StrictMono = StrictMono
 { multBy2ToThe :: Int
 , monotone :: Monotone
 } deriving Eq

instance Show StrictMono where
  show (StrictMono 0 m) = show m
  show (StrictMono n m) = let a = "2^" ++ show n
                              b = show (2 ^ n)
                          in (minimumBy (comparing length) [b,a]) ++ " * " ++ show m

data Monotone
 = Linear VVar
 | Full StrictMono
 deriving Eq

instance Show Monotone where
  show (Linear v) = show v
  show (Full sm) = "2^(" ++ show sm ++ ") - 1"

-- Reference semantics for NumValue types
class NumFun t where
  numEval :: t -> Integer -> Integer
  numValue :: t -> NumValue

instance NumFun NumValue where
  numEval NumValue{..} = ((fromIntegral upshift) +) . numEval grower
  numValue = id

instance NumFun Fun00 where
  numEval Constant0 = const 0
  numEval (StrictMonoFun mono) = numEval mono

  numValue = NumValue 0

instance NumFun StrictMono where
  numEval StrictMono{..} = ((2 ^ multBy2ToThe) *) . numEval monotone

  numValue = numValue . StrictMonoFun

instance NumFun Monotone where
  numEval (Linear _) = id
  numEval (Full sm) = full . numEval sm
   where
    full n = 2 ^ n - 1

  numValue = numValue . StrictMono 0

-- Actual semantics for NumValue types
nVar :: VVar -> NumValue
nVar v = NumValue
  { upshift = 0
  , grower = StrictMonoFun
             (StrictMono
               { multBy2ToThe = 0
               , monotone = Linear v
               })
  }

nConstant :: Int -> NumValue
nConstant n = NumValue n Constant0

nZero :: NumValue
nZero = nConstant 0

nPlus :: Int -> NumValue -> NumValue
nPlus n (NumValue up g) = NumValue (up + n) g

n2PowTimes :: Int -> NumValue -> NumValue
n2PowTimes n NumValue{..}
  = NumValue { upshift = upshift * (2 ^ n)
             , grower  = mult2PowGrower grower
             }
 where
  mult2PowGrower Constant0 = Constant0
  mult2PowGrower (StrictMonoFun sm)
   = StrictMonoFun (sm { multBy2ToThe = n + multBy2ToThe sm })

nFull :: NumValue -> NumValue
nFull NumValue{..} = case upshift of
  0 -> case grower of
    Constant0 -> NumValue 1 Constant0
    StrictMonoFun sm -> NumValue 0 (StrictMonoFun (StrictMono 0 (Full sm)))
  n -> n2PowTimes 1 (nFull (NumValue (n - 1) grower))

pattern TNat, TInt, TFloat, TBool, TText, TUnit, TNil :: Value
pattern TNat = VCon  (PrefixName [] "Nat") []
pattern TInt = VCon  (PrefixName [] "Int") []
pattern TFloat = VCon (PrefixName [] "Float") []
pattern TBool = VCon  (PrefixName [] "Bool") []
pattern TText = VCon (PrefixName [] "String") []
pattern TUnit = VCon (PrefixName [] "nil") []
pattern TNil = VCon (PrefixName [] "nil") []

pattern TList, TOption :: Value -> Value
pattern TList ty = VCon (PrefixName [] "List") [ty]
pattern TOption ty = VCon (PrefixName [] "Option") [ty]

pattern TVec, TCons :: Value -> Value -> Value
pattern TVec ty n = VCon (PrefixName [] "Vec") [ty, n]
pattern TCons x ys = VCon (PrefixName [] "cons") [x, ys]

instance Show Value where
  show v@(VCon _ _) | Just vs <- asList v = show vs
   where
    asList (VCon (PrefixName [] "nil") []) = Just []
    asList (VCon (PrefixName [] "cons") [hd, tl]) = (hd:) <$> asList tl
    asList _ = Nothing
  show (VCon c []) = show c
  show (VCon c vs) = show c ++ "(" ++ intercalate ", " (show <$> vs) ++ ")"
  show (VNum v) = show v
  show (VFun Braty _ (ss :-> ts)) = unwords [showSig ss, "->", showSig ts]
  show (VFun Kerny _ (ss :-> ts)) = unwords [showSig ss, "-o", showSig ts]
  show (VApp v ctx) = "VApp " ++ show v ++ " " ++ show ctx
  show (VLam ctx x) = "VLam " ++ show ctx ++ " " ++ show x

data Value {- n -} where -- n free de Bruijn indices
 VNum :: NumValue {- n -} -> Value {- n -}
 VCon :: UserName -> [Value {- n -}] -> Value {- n -}
 VApp :: VVar {- n -} -> Bwd (Value {- n -}) -> Value {- n -}
 -- Closure
 VLam :: Bwd {- length: m -} (Value {- 0 -})
      -> Value {- n + m + 1 -}
      -> Value {- n -}
 VFun :: Modey m
      -> Bwd {- length: l -} (Value {- 0 -})
      -> CType' (PortName, BinderType m) {- n + l -}
      -> Value {- n -}

type SValue = SType' Value

type family BinderType (m :: Mode) where
  BinderType Brat = KindOr Value
  BinderType Kernel = SValue

class EvenOrOdd t where
  -- When half t is (n, b), then t = 2*n+b. I.e. True means odd
  half :: t -> Maybe (NumValue, Bool)

instance EvenOrOdd NumValue where
  half (NumValue upshift grower) = case (upshift `divMod` 2, half grower) of
    ((up, 0), Just (n, False)) -> Just (nPlus up n, False)
    ((up, 0), Just (n, True))  -> Just (nPlus up n, True)
    ((up, 1), Just (n, False)) -> Just (nPlus up n, True)
    ((up, 1), Just (n, True))  -> Just (nPlus (up + 1) n, False)
    _ -> Nothing

instance EvenOrOdd Fun00 where
  half Constant0 = Just (nZero, False)
  half (StrictMonoFun sm) = half sm

instance EvenOrOdd StrictMono where
  half sm@StrictMono{..}
    | multBy2ToThe > 0 = Just (numValue (sm { multBy2ToThe = multBy2ToThe - 1 })
                              ,False)
    | otherwise = half monotone

instance EvenOrOdd Monotone where
  half _ = Nothing

data ValPat
 = VPVar
 | VPCon UserName [ValPat]
 | VPNum NumPat
 deriving Show

data NumPat
 = NP0
 | NP1Plus NumPat
 | NP2Times NumPat
 | NPVar
 deriving Show

numMatch :: Bwd Value -- Stuff we've already matched
         -> NumValue -- Type argument
         -> NumPat -- Pattern to match against arg
         -> Either ErrorMsg (Bwd Value)
numMatch zv arg NPVar = pure (zv :< VNum arg)
numMatch zv arg NP0
  | arg == nZero = pure zv
  | otherwise = Left $ NumMatchFail "0" (show arg)
numMatch zv arg@NumValue{upshift = upshift} (NP1Plus np)
  | upshift > 0 = numMatch zv (arg { upshift = upshift - 1 }) np
  | otherwise = Left $ NumMatchFail "1 + n" (show arg)
numMatch zv arg (NP2Times np)
  | Just (h, False) <- half arg
  = numMatch zv h np
  | otherwise = Left $ NumMatchFail "2 * n" (show arg)

valMatch :: Value -- Type argument
         -> ValPat -- Pattern to match against arg
         -> Either ErrorMsg (Bwd Value)
valMatch = valMatch' B0

valMatches :: [Value] -- Type argument
           -> [ValPat] -- Pattern to match against arg
           -> Either ErrorMsg (Bwd Value)
valMatches = valMatches' B0

-- internal version has an accumulator first arg
valMatch' :: Bwd Value -> Value -> ValPat -> Either ErrorMsg (Bwd Value)
valMatch' zv arg VPVar = pure (zv :< arg)
valMatch' zv (VCon u args) (VPCon u' vps)
  | u == u' = valMatches' zv args vps
  | otherwise = Left $ ValMatchFail (show u') (show u)
valMatch' zv (VNum n) (VPNum np) = numMatch zv n np
valMatch' _ v vp = error $ "valMatch called on " ++ show v ++ " " ++ show vp

valMatches' :: Bwd Value -> [Value] -> [ValPat] -> Either ErrorMsg (Bwd Value)
valMatches' zv [] [] = pure zv
valMatches' zv (v:vs) (p:ps) = do
  zv <- valMatch' zv v p
  valMatches' zv vs ps
valMatches' _ _ _ = Left $ InternalError "ragged lists in valMatches"


data VarChanger
  -- The Bwd list replaces the outermost de Bruijn indices
  = InxToPar (Bwd End)
  | ParToInx (Bwd End)
  | InxToLvl (Bwd (Int, TypeKind))

class DeBruijn t where
  -- The number counts the binders that we've gone under
  changeVar :: VarChanger -> Int -> t -> t

instance DeBruijn VVar where
  changeVar (InxToPar ends) i (VInx j) | j >= i = VPar (ends !< (j - i))
  changeVar (ParToInx ends) i (VPar e) | Just j <- findUnder e ends = VInx (i + j)
  changeVar (InxToLvl lvls) i (VInx j) | j >= i = uncurry VLvl (lvls !< (j - i))
  changeVar _ _ x = x

instance DeBruijn Value where
  changeVar vc i (VNum n) = VNum (changeVar vc i n)
  changeVar vc i (VCon c vs) = VCon c ((changeVar vc i) <$> vs)
  changeVar vc i (VApp v ss)
    = VApp (changeVar vc i v) (changeVar vc i <$> ss)
  changeVar vc i (VLam ctx v)
    = VLam ctx (changeVar vc (i + 1 + length ctx) v)
  changeVar vc i (VFun m@Braty ctx cty)
    = VFun m ctx $ changeVars vc i (doesItBind m) cty
  changeVar vc i (VFun m@Kerny ctx cty)
    = VFun m ctx $ changeVars vc i (doesItBind m) cty

changeVars :: (DeBruijn v, Traversable t)
           => VarChanger
           -> Int
           -> (v -> Maybe TypeKind)
           -> t (PortName, v)
           -> t (PortName, v)
changeVars vc i f xs = evalState (changeVars' f xs) i
 where
  changeVars' :: (DeBruijn v, Traversable t)
              => (v -> Maybe TypeKind)
              -> t (PortName, v)
              -> State Int (t (PortName, v))
  changeVars' f = traverse $ \(p,t) -> do
    i <- get
    let t' = changeVar vc i t
    when (isJust (f t)) $ put (i + 1)
    pure (p, t')

instance DeBruijn NumValue where
  changeVar vc i (NumValue u g) = NumValue u (changeVar vc i g)

instance DeBruijn Fun00 where
  changeVar _ _ Constant0 = Constant0
  changeVar vc i (StrictMonoFun sm) = StrictMonoFun (changeVar vc i sm)

instance DeBruijn StrictMono where
  changeVar vc i (StrictMono pow mono) = StrictMono pow (changeVar vc i mono)

instance DeBruijn Monotone where
  changeVar vc i (Linear v) = Linear (changeVar vc i v)
  changeVar vc i (Full sm) = Full (changeVar vc i sm)

instance (DeBruijn s, DeBruijn t) => DeBruijn (Either s t) where
  changeVar vc i (Left s) = Left $ changeVar vc i s
  changeVar vc i (Right t) = Right $ changeVar vc i t

instance DeBruijn PortName where
  changeVar _ _ = id

instance DeBruijn TypeKind where
  changeVar _ _ = id

instance DeBruijn t => DeBruijn (SType' t) where
  changeVar vc i (Of ty n) = Of (changeVar vc i ty) (changeVar vc i n)
  changeVar vc i (Rho (R row)) = Rho (R (second (changeVar vc i) <$> row))
  changeVar _ _ sty = sty

instance DeBruijn (Term d k) where
  changeVar vc i (Inx j) =
    case changeVar vc i (VInx j) of
      VPar e -> Par e
      VInx j -> Inx j
  changeVar vc i (Par e) =
    case changeVar vc i (VPar e) of
      VPar e -> Par e
      VInx j -> Inx j
  changeVar vc i (Let abs stuff x) = Let abs (changeVar vc i <$> stuff) (changeVar vc i <$> x)
  changeVar vc i (a :|: b)
   = (changeVar vc i <$> a) :|: (changeVar vc i <$> b)
  changeVar vc i (Th x) = Th $ changeVar vc i <$> x
  changeVar vc i (Force x) = Force $ changeVar vc i <$> x
  changeVar vc i (Emb x) = Emb (changeVar vc i <$> x)
  changeVar vc i (Pull ps x) = Pull ps $ changeVar vc i <$> x
  changeVar vc i (f :$: a)
   = (changeVar vc i <$> f) :$: (changeVar vc i <$> a)
  changeVar vc i (tm ::: ty) = (changeVar vc i <$> tm) ::: (second (fmap (changeVar vc i)) <$> ty)
  changeVar vc i (top :-: bot)
   = (changeVar vc i <$> top) :-: (changeVar vc i <$> bot)
  -- trouble?
  changeVar vc i (abs :\: body) = abs :\: (changeVar vc i <$> body)
  changeVar vc i (Con u args) = Con u $ changeVar vc i <$> args
  changeVar vc i (C cty) = C (changeVars vc i doesItBind2 cty)

  changeVar vc i (K (R ss) (R ts))
    = K (R (second (changeVar vc i) <$> ss))
        (R (second (changeVar vc i) <$> ts))
  changeVar _ _ tm = tm

doesItBind2 :: KindOr a -> Maybe TypeKind
doesItBind2 (Left k) = Just k
doesItBind2 _ = Nothing

doesItBind :: Modey m -> BinderType m -> Maybe TypeKind
doesItBind Braty (Left k) = Just k
doesItBind _ _ = Nothing

endVal :: TypeKind -> End -> Value
endVal k e = varVal k (VPar e)

varVal :: TypeKind -> VVar -> Value
varVal Nat v = VNum (nVar v)
varVal _ v = VApp v B0
