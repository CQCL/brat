{-# LANGUAGE
EmptyCase,
FlexibleContexts,
QuantifiedConstraints,
ScopedTypeVariables,
UndecidableInstances
#-}

module Brat.Syntax.Value {-(VDecl
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
                         ,FunVal(..), value
                         )-} where

import Brat.Error
import Brat.Syntax.Common
import Brat.Syntax.Core (Term (..))
import Brat.UserName
import Bwd
import Hasochism

import Data.List (intercalate, minimumBy)
import Data.Ord (comparing)
import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..))

newtype VDecl = VDecl (Decl' (Some (Flip (Ro' Brat) Z)) (FunBody Term Noun))

instance MODEY Brat => Show VDecl where
  show (VDecl decl) = show $ aux decl
   where
    aux :: Decl' (Some (Flip (Ro' Brat) Z)) body -> Decl' String body
    aux (Decl { .. }) = case fnSig of
      Some sig -> Decl { fnName = fnName, fnSig = (show sig), fnBody = fnBody, fnLoc = fnLoc, fnRT = fnRT, fnLocality = fnLocality }

------------------------------------ Values ------------------------------------
-- Well scoped de Bruijn indices
data Inx :: N -> Type where
  -- We need `S n`, to say that there are >0 variables to choose the 0th from
  VZ :: Inx (S n)
  VS :: Inx n -> Inx (S n)

instance Show (Inx n) where
  show = show . toNat
   where
    toNat :: forall n. Inx n -> Int
    toNat VZ = 0
    toNat (VS n) = 1 + (toNat n)

data AddR :: N -> N -> N -> Type where
  AddZ :: Ny out -> AddR out Z out
  AddS :: AddR out inn tot -> AddR out (S inn) (S tot)

-- If we have `out` outer variables on the left, then `inn` inner variables,
-- work out where a given `Inx` lies
outOrInn :: AddR out inn tot -> Inx tot -> Either (Inx out) (Inx inn)
-- There are no inner variables (because of AddZ), so everything lives in outer
outOrInn (AddZ _) inx = Left inx
-- There is at least 1 inner variable (because of AddS), so VZ is inner
outOrInn (AddS _) (VZ {- :: Inx (S tot) -}) = Right (VZ {- Inx (S inn) -})
outOrInn (AddS a) (VS inx) = case outOrInn a inx of
  -- inx is inner, put the VS back
  Right (inx {- :: Inx inn -}) -> Right ((VS inx) {- :: Inx (S inn) -})
  -- inx is outer, we don't care how many inner vars we passed to get to it
  Left (inx {- :: Inx out -}) -> Left (inx {- :: Inx out -})

injOut :: AddR out inn tot -> Inx out -> Inx tot
injOut (AddZ _) v = v
injOut (AddS a) v = VS $ injOut a v

injInn :: AddR out inn tot -> Inx inn -> Inx tot
injInn (AddZ _) v = impossible v
injInn (AddS _) VZ = VZ
injInn (AddS a) (VS v) = VS $ injInn a v

impossible :: Inx Z -> a
impossible v = case v of {}

findInx :: Eq x => Stack Z x n -> x -> Maybe (Inx n)
findInx S0 _ = Nothing
findInx (xz :<< x) x'
  | x == x' = Just VZ
  | otherwise = VS <$> findInx xz x'

data Stack :: N -> Type -> N -> Type where
  S0 :: Stack n x n
  (:<<) :: Stack n x m -> x -> Stack n x (S m)
infixl 7 :<<
deriving instance Show t => Show (Stack n t m)

-- Having a valid `Inx n` guarantees the Stack isn't empty
proj :: Stack Z x n -> Inx n -> x
proj S0 v = impossible v
proj (_ :<< x) VZ = x
proj (stk :<< _) (VS i) = proj stk i

(<<+) :: Stack l x n -> Stack n x m -> Stack l x m
S0 <<+ stk = stk
stk <<+ S0 = stk
stk <<+ (stk' :<< x) = stk <<+ stk' :<< x

infixr 8 <<+

-- Environment of closed values of size `top`
type Valz = Stack Z (Val Z)

type family ValueType (m :: Mode) :: N -> Type where
  ValueType Brat = Val
  ValueType Kernel = SVal

data VVar :: N -> Type where
  VPar :: End -> VVar n  -- Has to be declared in the Store (for equality testing)
  VLvl :: Int -> TypeKind -> VVar n  -- Cache the kind for equality testing
  VInx :: Inx n -> VVar n

deriving instance Show (VVar n)

instance Eq (VVar n) where
  (VLvl i0 k0) == (VLvl i1 k1) = i0 == i1 && k0 == k1
  (VPar e0) == (VPar e1) = e0 == e1
  (VInx _) == (VInx _) = error "tried to compare VInxs"
  _ == _ = False

data Scope :: (N -> Type) -> (N -> Type) where
  (::-) :: Stack n (Val Z) m -- Inx-closed values from n to m (stashed env)
        -> f (S m)           -- Plus an `f` with 1 extra lambda-bound variable
        -> Scope f n

infix 6 ::-

deriving instance (forall n. Show (f n)) => Show (Scope f n)

data Val :: N -> Type where
  VNum :: NumVal n -> Val n
  VCon :: UserName -> [Val n] -> Val n
  VLam :: Scope Val n -> Val n
  VFun :: Modey m -> CTy m n -> Val n
  VApp :: VVar n -> Bwd (Val n) -> Val n

data CTy :: Mode -> N -> Type where
  (:->>) :: Ro m i j -> Ro m j k -> CTy m i

instance MODEY m => Show (CTy m n) where
  show (ri :->> ro) = unwords [show ri, arrow, show ro]
   where
    arrow = case modey :: Modey m of
      Braty -> "->"
      Kerny -> "-o"

-- The `Ro` that we should always use, because the number of free variables grows on the right
type Ro m bot top = Ro' m top bot

-- Ro with top and bottom the wrong way round for partial application
data Ro' :: Mode
        -> N -- The number of free variables at the end (top)
        -> N -- The number of free variables at the start (bottom)
        -> Type where
  R0 :: Ro m bot bot
  -- Existential quantification
  REx :: (PortName, TypeKind)
      -> Scope (Ro' Brat top) bot -- This why top and bot have to be backwards
      -> Ro Brat bot top
  -- Pairing
  RPr :: (PortName, ValueType m bot) -> Ro m bot top -> Ro m bot top

instance forall m top bot. MODEY m => Show (Ro' m top bot) where
  show ro = intercalate ", " $ roToList ro
   where
    roToList :: forall bot. Ro' m top bot -> [String]
    roToList R0 = []
    roToList (RPr (p, ty) ro) = let tyStr = case modey :: Modey m of
                                      Braty -> show ty
                                      Kerny -> show ty
                                in  ('(':p ++ " :: " ++ tyStr ++ ")"):roToList ro
    roToList  (REx (p, k) (_ ::- ro)) = ('(':p ++ " :: " ++ show k ++ ")"):roToList ro

-------------------------------- Number Values ---------------------------------
data NumVal n = NumValue
  { upshift :: Int
  , grower  :: Fun00 n
  } deriving Eq

instance Show (NumVal n) where
  show (NumValue 0 g) = show g
  show (NumValue n Constant0) = show n
  show (NumValue n g) = show n ++ " + " ++ show g

-- Functions which map 0 to 0
data Fun00 n
 = Constant0
 | StrictMonoFun (StrictMono n)
 deriving Eq

instance Show (Fun00 n) where
  show Constant0 = "0"
  show (StrictMonoFun sm) = show sm

-- Strictly increasing function
data StrictMono n = StrictMono
 { multBy2ToThe :: Int
 , monotone :: Monotone n
 } deriving Eq

instance Show (StrictMono n) where
  show (StrictMono 0 m) = show m
  show (StrictMono n m) = let a = "2^" ++ show n
                              b = show (2 ^ n :: Int)
                          in (minimumBy (comparing length) [b,a]) ++ " * " ++ show m

data Monotone n
 = Linear (VVar n)
 | Full (StrictMono n)
 deriving Eq

instance Show (Monotone n) where
  show (Linear v) = show v
  show (Full sm) = "2^(" ++ show sm ++ ") - 1"

-- Reference semantics for NumValue types
class NumFun (t :: N -> Type) where
  numEval :: t n -> Integer -> Integer
  numValue :: t n -> NumVal n

instance NumFun NumVal where
  numEval NumValue{..} = ((fromIntegral upshift) +) . numEval grower
  numValue = id

instance NumFun Fun00 where
  numEval Constant0 = const 0
  numEval (StrictMonoFun mono) = numEval mono

  numValue fun00 = NumValue 0 fun00

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
nVar :: VVar n -> NumVal n
nVar v = NumValue
  { upshift = 0
  , grower = StrictMonoFun
             (StrictMono
               { multBy2ToThe = 0
               , monotone = Linear v
               })
  }

nConstant :: Int -> NumVal n
nConstant n = NumValue n Constant0

nZero :: NumVal n
nZero = nConstant 0

nPlus :: Int -> NumVal n -> NumVal n
nPlus n (NumValue up g) = NumValue (up + n) g

n2PowTimes :: Int -> NumVal n -> NumVal n
n2PowTimes n NumValue{..}
  = NumValue { upshift = upshift * (2 ^ n)
             , grower  = mult2PowGrower grower
             }
 where
  mult2PowGrower Constant0 = Constant0
  mult2PowGrower (StrictMonoFun sm)
   = StrictMonoFun (sm { multBy2ToThe = n + multBy2ToThe sm })

nFull :: NumVal n -> NumVal n
nFull NumValue{..} = case upshift of
  0 -> case grower of
    Constant0 -> NumValue 1 Constant0
    StrictMonoFun sm -> NumValue 0 (StrictMonoFun (StrictMono 0 (Full sm)))
  n -> n2PowTimes 1 (nFull (NumValue (n - 1) grower))

pattern TNat, TInt, TFloat, TBool, TText, TUnit, TNil :: Val n
pattern TNat = VCon  (PrefixName [] "Nat") []
pattern TInt = VCon  (PrefixName [] "Int") []
pattern TFloat = VCon (PrefixName [] "Float") []
pattern TBool = VCon  (PrefixName [] "Bool") []
pattern TText = VCon (PrefixName [] "String") []
pattern TUnit = VCon (PrefixName [] "nil") []
pattern TNil = VCon (PrefixName [] "nil") []

pattern TList, TOption :: Val n -> Val n
pattern TList ty = VCon (PrefixName [] "List") [ty]
pattern TOption ty = VCon (PrefixName [] "Option") [ty]

pattern TVec, TCons :: Val n -> Val n -> Val n
pattern TVec ty n = VCon (PrefixName [] "Vec") [ty, n]
pattern TCons x ys = VCon (PrefixName [] "cons") [x, ys]

instance Show (Val n) where
  show v@(VCon _ _) | Just vs <- asList v = show vs
   where
    asList (VCon (PrefixName [] "nil") []) = Just []
    asList (VCon (PrefixName [] "cons") [hd, tl]) = (hd:) <$> asList tl
    asList _ = Nothing
  show (VCon c []) = show c
  show (VCon c vs) = show c ++ "(" ++ intercalate ", " (show <$> vs) ++ ")"
  show (VNum v) = show v
  -- FIXME
  show (VFun m cty) = "{ " ++ modily m (show cty) ++ " }"
  show (VApp v ctx) = "VApp " ++ show v ++ " " ++ show ctx
  show (VLam (ga ::- x)) = "VLam " ++ show ga ++ " " ++ show x

type SValue = SVal Z

type family BinderType (m :: Mode) where
  BinderType Brat = KindOr (Val Z)
  BinderType Kernel = SVal Z

type family BinderVal (m :: Mode) where
  BinderVal Brat = Val Z
  BinderVal Kernel = KernelVal Z

-- EvenOrOdd attempts to do DivMod to a numval.
-- It shouldn't change the number of free variables
class EvenOrOdd (t :: N -> Type) where
  -- When half t is (n, b), then t = 2*n+b. I.e. True means odd
  half :: t n -> Maybe (NumVal n, Bool)

instance EvenOrOdd NumVal where
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

bwdStack :: Bwd x -> Some (Ny :* Stack Z x)
bwdStack B0 = Some (Zy :* S0)
bwdStack (zx :< x) = case bwdStack zx of
  Some (ny :* stk) -> Some (Sy ny :* (stk :<< x))

numMatch :: Bwd (Val Z) -- Stuff we've already matched
         -> NumVal Z -- Type argument
         -> NumPat -- Pattern to match against arg
         -> Either ErrorMsg (Bwd (Val Z))
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

valMatch :: Val Z -- Type argument
         -> ValPat -- Pattern to match against arg
         -> Either ErrorMsg (Some (Ny :* Valz))
valMatch val pat = bwdStack <$> valMatch' B0 val pat

valMatches :: [Val Z] -- Type argument
           -> [ValPat] -- Pattern to match against arg
           -> Either ErrorMsg (Some (Ny :* Valz))
valMatches vals pats = bwdStack <$> valMatches' B0 vals pats

-- internal version has an accumulator first arg
valMatch' :: Bwd (Val Z) -> Val Z -> ValPat -> Either ErrorMsg (Bwd (Val Z))
valMatch' zv arg VPVar = pure (zv :< arg)
valMatch' zv (VCon u args) (VPCon u' vps)
  | u == u' = valMatches' zv args vps
  | otherwise = Left $ ValMatchFail (show u') (show u)
valMatch' zv (VNum n) (VPNum np) = numMatch zv n np
valMatch' _ v vp = error $ "valMatch called on " ++ show v ++ " " ++ show vp

valMatches' :: Bwd (Val Z) -> [Val Z] -> [ValPat] -> Either ErrorMsg (Bwd (Val Z))
valMatches' zv [] [] = pure zv
valMatches' zv (v:vs) (p:ps) = do
  zv <- valMatch' zv v p
  valMatches' zv vs ps
valMatches' _ _ _ = Left $ InternalError "ragged lists in valMatches"


class DeBruijn (t :: N -> Type) where
  -- Change the scope of Inx variables
  changeVar :: VarChanger src tgt -> t src -> t tgt

-- Intended solely for use by the DeBruijn typeclass.
-- The two Nat parameters correspond to the src and tgt scope respectively
data VarChanger :: N -> N -> Type where
  InxToPar :: AddR out inn tot   -- Proof that src - tgt = out
           -> Stack Z End out    -- Ends for each variable in outer scope
           -> VarChanger tot inn -- Reduce the scope by changing outer vars
  ParToInx :: AddR out inn tot
           -> Stack Z End out    -- Ends for each outer variable we want to abstract (by matching on the End)
           -> VarChanger inn tot -- Expand scope by abstract outer Par variables
  InxToLvl :: AddR out inn tot
           -> Stack Z (Int, TypeKind) out -- de Bruijn level for every outer variable
           -> VarChanger tot inn

weakenVC :: VarChanger src tgt -> VarChanger (S src) (S tgt)
weakenVC (InxToPar a stk) = InxToPar (AddS a) stk
weakenVC (ParToInx a stk) = ParToInx (AddS a) stk
weakenVC (InxToLvl a stk) = InxToLvl (AddS a) stk


instance DeBruijn VVar where
  changeVar (InxToPar a endz) (VInx v) = case outOrInn a v of
    Left out -> VPar (proj endz out)
    Right inn -> VInx inn
  changeVar (ParToInx a endz) (VPar e)
    | Just out <- findInx endz e = VInx (injOut a out)
  -- Need to update the scope of inner variables, since we're adding more outers
  changeVar (ParToInx a _) (VInx v) = VInx (injInn a v)
  changeVar (InxToLvl a lvlz) (VInx v) = case outOrInn a v of
    Left out -> uncurry VLvl (proj lvlz out)
    Right inn -> VInx inn
  changeVar _ (VPar e) = VPar e
  changeVar _ (VLvl l k) = VLvl l k

-- Invariant: tgt - src = tgt' - src' (varchanger makes the same change to the scope)
-- Hence:     tgt' - tgt = src' - src (the stack has the same length)
varChangerThroughStack :: VarChanger src tgt
                       -> Stack src x src'
                       -> Some (VarChanger src' -- VarChanger src' tgt' (weakened by the length of the stack)
                                :*
                                Stack tgt x -- Stack tgt x tgt' (shifted by the scope difference of the VarChanger)
                               )
varChangerThroughStack (vc {- src -> tgt -}) (S0 {- src = src' -}) = Some {- tgt' = tgt -} (vc {- src' -> tgt' -} :* S0)
varChangerThroughStack (vc {- src -> tgt -}) (xz :<< x {- src -> S src' -}) = case varChangerThroughStack vc xz of
  Some {- tgt' -} (vc {- src' -> tgt' -} :* xz {- tgt -> tgt' -}) -> Some {- S tgt' -} ((weakenVC vc {- S src' -> S tgt' -}) :* ((xz :<< x) {- tgt -> S tgt' -}))

instance DeBruijn t => DeBruijn (Scope t) where
  changeVar vc (vz ::- t) = case varChangerThroughStack vc vz of
    Some (vc :* vz) -> vz ::- changeVar (weakenVC vc) t

instance DeBruijn Val where
  changeVar vc (VNum n) = VNum (changeVar vc n)
  changeVar vc (VCon c vs) = VCon c ((changeVar vc) <$> vs)
  changeVar vc (VApp v ss)
    = VApp (changeVar vc v) (changeVar vc <$> ss)
  changeVar vc (VLam sc)
    = VLam (changeVar vc sc)
  changeVar vc (VFun Braty cty)
    = VFun Braty $ changeVar vc cty
  changeVar vc (VFun Kerny cty)
    = VFun Kerny $ changeVar vc cty

varChangerThroughRo :: DeBruijn (ValueType m)
                    => VarChanger src tgt
                    -> Ro m src src'
                    -> Some (VarChanger src' -- VarChanger src' tgt'
                             :*
                             Flip (Ro' m) tgt -- Ro m tgt tgt'
                            )
-- Lift the scope of Ro from src -> src' to tgt -> tgt'
-- R0 enforces src = src', so we choose tgt' = tgt in our existential type
varChangerThroughRo vc R0 = Some (vc :* Flip R0)
varChangerThroughRo vc (RPr (p,ty) ro {- src -> src' -}) = case changeVar vc {- src -> tgt -} ty of
  ty -> case varChangerThroughRo vc ro of
          Some (vc {- src' -> tgt' -} :* Flip ro {- tgt -> tgt' -}) -> Some (vc :* Flip (RPr (p,ty) ro))
varChangerThroughRo vc {- src -> tgt -} (REx pk (vz {- src -> src' -} ::- ro {- S src' -> src'' -}))
  -- First, go through the let-bound stack
  = case varChangerThroughStack vc vz of
      -- Second, go through the lambda for the existential. Third, go through the rest of the row
      Some (vc {- src' -> tgt' -} :* vz {- tgt -> tgt' -}) -> case varChangerThroughRo (weakenVC vc) ro of
        Some (vc {- src'' -> tgt'' -} :* Flip ro {- S tgt' -> tgt'' -}) -> Some (vc :* Flip (REx pk (vz ::- ro)))

instance DeBruijn (ValueType m) => DeBruijn (CTy m) where
  changeVar (vc {- srcIn -> tgtIn -}) (ri {- srcIn -> srcMid -} :->> ro {- srcMid -> srcOut -}) = case varChangerThroughRo vc ri of
    Some {- tgtMid -} (vc {- srcMid -> tgtMid -} :* Flip ri {- tgtIn -> tgtMid -}) -> case varChangerThroughRo vc ro of
      Some {- tgtOut -} (_vc {- srcOut -> tgtOut -} :* Flip ro {- tgtMid -> tgtOut -}) -> ri :->> ro

instance DeBruijn NumVal where
  changeVar vc (NumValue u g) = NumValue u (changeVar vc g)

instance DeBruijn Fun00 where
  changeVar _ Constant0 = Constant0
  changeVar vc (StrictMonoFun sm) = StrictMonoFun (changeVar vc sm)

instance DeBruijn StrictMono where
  changeVar vc (StrictMono pow mono) = StrictMono pow (changeVar vc mono)

instance DeBruijn Monotone where
  changeVar vc (Linear v) = Linear (changeVar vc v)
  changeVar vc (Full sm) = Full (changeVar vc sm)


instance DeBruijn SVal where
  changeVar vc (VOf ty n) = VOf (changeVar vc ty) (changeVar vc n)
  changeVar (vc {- src -> tgt -}) (VRho ro {- src -> src -}) = case varChangerThroughRo vc ro of
    Some {- tgt' -} (_vc {- src -> tgt' -} :* Flip ro {- tgt -> tgt' -})
      | Refl <- kernelNoBind ro {- tgt = tgt' -} -> VRho ro
  changeVar _ VQ = VQ
  changeVar _ VBit = VBit

kernelNoBind :: Ro Kernel bot top -> bot :~: top
kernelNoBind R0 = Refl
kernelNoBind (RPr _ ro) = kernelNoBind ro

endVal' :: Modey m -> BinderType m -> End -> BinderVal m
endVal' Braty (Left Nat) e = VNum (nVar (VPar e))
endVal' Braty _ e = VApp (VPar e) B0
endVal' Kerny _ e = KVar (VPar e)

endVal :: TypeKind -> End -> Val Z
endVal k e = varVal k (VPar e)

varVal :: TypeKind -> (VVar n) -> Val n
varVal Nat v = VNum (nVar v)
varVal _ v = VApp v B0

-- TODO: Rename this to KernelType or similar
data SVal :: N -> Type where
  VQ   :: SVal n
  VBit :: SVal n
  VOf  :: SVal n -> NumVal n -> SVal n
  -- We're not allowed any binding constructs in a kernel row (no `REx`s)
  VRho :: Ro Kernel n n -> SVal n

instance Show (SVal n) where
  show VQ = "Qubit"
  show VBit = "Bool"
  show (VOf ty n) = "Vec(" ++ show ty ++ ", " ++ show n ++ ")"
  show (VRho ro) = show ro

data KernelVal :: N -> Type where
  KVar  :: VVar n -> KernelVal n
  KBit  :: Bool -> KernelVal n
  KNil  :: KernelVal n
  KCons :: KernelVal n -> KernelVal n -> KernelVal n
deriving instance Show (KernelVal n)

type FunVal m = CTy m Z
--value :: Modey m -> FunVal m -> Val Z
--value = VFun

roTop :: Ny bot -> Ro Brat bot top -> Ny top
roTop ny R0 = ny
roTop ny (RPr _ ro) = roTop ny ro
roTop ny (REx _ (stk ::- ro)) = roTop (Sy (stkTop ny stk)) ro
 where
  stkTop :: Ny bot -> Stack bot ty top -> Ny top
  stkTop ny S0 = ny
  stkTop ny (stk :<< _) = Sy (stkTop ny stk)

stkLen :: Stack Z t tot -> Ny tot
stkLen S0 = Zy
stkLen (zx :<< _) = Sy (stkLen zx)
