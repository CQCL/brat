module Brat.Constructors where

import qualified Data.Map as M

import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.UserName
import Bwd
import Hasochism (N(..), Ny(..))

-- TODO: Enforce the invariant that the number of pattern variables is n
data CtorArgs m where
  CArgs :: [ValPat] -- Patterns to match the arguments to Ty against
        -> Ny i        -- Number of pattern variables bound (natEqOrBust will test this)
        -> Ro Brat Z i  -- Kinds of pattern variables
        -> Ro m i j -- Inputs for the constructor node, which we should feed C's args into
        -- N.B. these can include bound variables which refer to things bound by
        -- matching the patterns in the `[ValPat]` against Ty's arguments.
        -> CtorArgs m

type ConstructorMap m
  = M.Map UserName  -- The name of a constructor "C"
    (M.Map UserName -- The name of the type we're checking against "Ty"
     (CtorArgs m)
    )

pattern CSucc, CDoub, CNil, CCons, CSome, CNone, CTrue, CFalse, CZero, CSnoc :: UserName
pattern CSucc = PrefixName [] "succ"
pattern CDoub = PrefixName [] "doub"
pattern CNil = PrefixName [] "nil"
pattern CCons = PrefixName [] "cons"
pattern CSome = PrefixName [] "some"
pattern CNone = PrefixName [] "none"
pattern CTrue = PrefixName [] "true"
pattern CFalse = PrefixName [] "false"
pattern CZero = PrefixName [] "zero"
pattern CSnoc = PrefixName [] "snoc"

pattern CList, CVec, CNat, CInt, COption, CBool, CBit, CFloat, CString :: UserName
pattern CList = PrefixName [] "List"
pattern CVec = PrefixName [] "Vec"
pattern CNat = PrefixName [] "Nat"
pattern CInt = PrefixName [] "Int"
pattern COption = PrefixName [] "Option"
pattern CBool = PrefixName [] "Bool"
pattern CBit = PrefixName [] "Bit"
pattern CFloat = PrefixName [] "Float"
pattern CString = PrefixName [] "String"

pattern CQubit, CMoney :: UserName
pattern CQubit = PrefixName [] "Qubit"
pattern CMoney = PrefixName [] "Money"

defaultConstructors :: ConstructorMap Brat
defaultConstructors = M.fromList
  [(CSucc, M.fromList
     [(CNat, CArgs [] Zy R0 (RPr ("value", TNat) R0))
     ,(CInt, CArgs [] Zy R0 (RPr ("value", TInt) R0))
     ])
  ,(CDoub, M.fromList
     [(CNat, CArgs [] Zy R0 (RPr ("value", TNat) R0))
     ,(CInt, CArgs [] Zy R0 (RPr ("value", TInt) R0))
     ])
  ,(CZero, M.fromList
     [(CNat, CArgs [] Zy R0 R0)
     ,(CInt, CArgs [] Zy R0 R0)
     ])
  ,(CNil, M.fromList
     [(CList, CArgs [VPVar] (Sy Zy) (REx ("elementType", Star []) (S0 ::- R0)) R0)
     ,(CVec, CArgs [VPVar, VPNum NP0] (Sy Zy) (REx ("elementType", Star []) (S0 ::- R0)) R0)
     ,(CNil, CArgs [] Zy R0 R0)
     ])
  ,(CCons, M.fromList
     [(CList, CArgs [VPVar] (Sy Zy)
       (REx ("elementType", Star []) (S0 ::- R0))
       (RPr ("head", VApp (VInx VZ) B0)
         (RPr ("tail", TList (VApp (VInx VZ) B0)) R0)))
     ,(CVec, CArgs [VPVar, VPNum (NP1Plus NPVar)] (Sy (Sy Zy))
       (REx ("elementType", Star []) (S0 ::- (REx ("tailLength", Nat) (S0 ::- R0))))
       (RPr ("head", VApp (VInx (VS VZ)) B0)
        (RPr ("tail", TVec (VApp (VInx (VS VZ)) B0) (VNum $ nVar (VInx VZ))) R0)))
     ,(CCons, CArgs [VPVar, VPCon (plain "nil") []] (Sy Zy)
       (REx ("elementType", Star []) (S0 ::- R0))
       (RPr ("value", VApp (VInx VZ) B0) R0))
     ,(CCons, CArgs [VPVar, VPVar] (Sy (Sy Zy))
       (REx ("headTy", Star [])
        (S0 ::- (REx ("tailTy", Star []) (S0 ::- R0))))
       (RPr ("head", VApp (VInx (VS VZ)) B0)
        (RPr ("tail", VApp (VInx VZ) B0) R0)))
     ])
  ,(CSnoc, M.fromList
     [(CList, CArgs [VPVar] (Sy Zy)
       (REx ("elementType", Star []) (S0 ::- R0))
       (RPr ("tail", TList (VApp (VInx VZ) B0))
        (RPr ("head", VApp (VInx VZ) B0) R0)))
     ,(CVec, CArgs [VPVar, VPNum (NP1Plus NPVar)] (Sy (Sy Zy))
       (REx ("elementType", Star []) (S0 ::- (REx ("tailLength", Nat) (S0 ::- R0))))
       (RPr ("tail", TVec (VApp (VInx (VS VZ)) B0) (VNum $ nVar (VInx VZ)))
        (RPr ("head", VApp (VInx (VS VZ)) B0) R0)))
     ])
  ,(CNone, M.fromList
     [(COption, CArgs [VPVar] (Sy Zy) (REx ("ty", Star []) (S0 ::- R0)) R0)])
  ,(CSome, M.fromList
     [(COption, CArgs [VPVar] (Sy Zy)
        (REx ("ty", Star []) (S0 ::- R0))
        (RPr ("value", VApp (VInx VZ) B0) R0))])
  ,(CTrue, M.fromList [(CBool, CArgs [] Zy R0 R0)])
  ,(CFalse, M.fromList [(CBool, CArgs [] Zy R0 R0)])
  ]

kernelConstructors :: ConstructorMap Kernel
kernelConstructors = M.fromList
  [(CNil, M.fromList
     [(CVec, CArgs [VPVar, VPNum NP0] (Sy Zy) (REx ("elementType", Dollar []) (S0 ::- R0)) R0)]
   )
  ,(CCons, M.fromList
     [(CVec, CArgs [VPVar, VPNum (NP1Plus NPVar)] (Sy (Sy Zy))
       (REx ("elementType", Dollar []) (S0 ::- (REx ("tailLength", Nat) (S0 ::- R0))))
       (RPr ("head", VApp (VInx (VS VZ)) B0)
        (RPr ("tail", TVec (VApp (VInx (VS VZ)) B0) (VNum $ nVar (VInx VZ))) R0)))
     ])
  ,(CSnoc, M.fromList
     [(CVec, CArgs [VPVar, VPNum (NP1Plus NPVar)] (Sy (Sy Zy))
       (REx ("elementType", Dollar []) (S0 ::- (REx ("tailLength", Nat) (S0 ::- R0))))
       (RPr ("tail", TVec (VApp (VInx (VS VZ)) B0) (VNum $ nVar (VInx VZ)))
        (RPr ("head", VApp (VInx (VS VZ)) B0) R0)))
     ])
  ,(CTrue, M.fromList [(CBit, CArgs [] Zy R0 R0)])
  ,(CFalse, M.fromList [(CBit, CArgs [] Zy R0 R0)])
  ]

defaultTypeConstructors :: M.Map (Mode, UserName) [(PortName, TypeKind)]
defaultTypeConstructors = M.fromList
  [((Brat, COption), [("value", Star [])])
  ,((Brat, CList),   [("listValue", Star [])])
  ,((Brat, CVec),    [("X", Star []), ("n", Nat)])
  ,((Brat, CBool),   [])
  ,((Brat, CBit),    [])
  ,((Brat, CInt),    [])
  ,((Brat, CFloat),  [])
  ,((Brat, CString), [])
  ,((Brat, CNat),    [])
  ,((Brat, CNil),    [])
  ,((Brat, CCons),   [("head", Star []), ("tail", Star [])])
  ,((Kernel, CQubit), [])
  ,((Kernel, CMoney), [])
  ,((Kernel, CVec), [("X", Dollar []), ("n", Nat)])
  ,((Kernel, CBit), [])
  ,((Kernel, CBool), [])
  ]

{-
-- TODO: Make type aliases more flexible. Allow different patterns and allow Nat
-- kinds. Allow port pulling when applying them
-- TODO: Aliases for kernel types
typeAliases :: M.Map UserName (Modey m, [ValPat], BinderType m)
typeAliases = M.empty
{- Here is an example, for `type Vec5(X) = Vec(X, n)`:
M.fromList $
  [(plain "Vec5", (Braty, [VPVar], Con (plain "Vec") (VInx VZ :|: (Simple (Num 5)))))]

-- TODO: There's no way to parse the above syntax as:
  [(plain "Vec5", (Kerny, [VPVar], Of (VInx VZ) (Simple (Num 5))))]
-}
-}

natConstructors :: M.Map UserName (Maybe NumPat, NumVal Z -> NumVal Z)
natConstructors = M.fromList
  [(plain "succ", (Just (NP1Plus NPVar)
                  ,nPlus 1))
  ,(plain "doub", (Just (NP2Times NPVar)
                  ,n2PowTimes 1))
  ,(plain "full", (Nothing, nFull))
  ,(plain "zero", (Just NP0, id))
  ]
