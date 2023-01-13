module Brat.Constructors (ConstructorMap
                         ,defaultConstructors
                         ,defaultTypeConstructors
                         ,natConstructors
                         ) where

import qualified Data.Map as M

import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.UserName
import Bwd

type ConstructorMap
  = M.Map UserName  -- The name of a constructor "C"
    (M.Map UserName -- The name of the type we're checking against "Ty"
     ([ValPat]      -- Patterns to match the arguments to Ty against
      -- Inputs for the constructor node, which we should feed C's args into
      -- N.B. these can include bound variables which refer to things bound by
      -- matching the patterns in the `[ValPat]` against Ty's arguments.
     ,[(PortName, BinderType Brat)]
     )
    )

defaultConstructors :: ConstructorMap
defaultConstructors = M.fromList
  [(plain "succ", M.fromList
     [(plain "Nat", ([], [("value", Right TNat)]))
     ,(plain "Int", ([], [("value", Right TInt)]))
     ])
  ,(plain "doub", M.fromList
     [(plain "Nat", ([], [("value", Right TNat)]))
     ,(plain "Int", ([], [("value", Right TInt)]))
     ])
  ,(plain "nil", M.fromList
     [(plain "List", ([VPVar], []))
     ,(plain "Vec", ([VPVar, VPNum NP0], []))
     ,(plain "nil", ([], []))
     ])
  ,(plain "cons", M.fromList
     [(plain "List"
      ,([VPVar]
       ,[("head", Right (VApp (VInx 0) B0))
        ,("tail", Right (TList (VApp (VInx 0) B0)))
        ]))
     ,(plain "Vec"
      ,([VPVar, VPNum (NP1Plus NPVar)]
       ,[("head", Right (VApp (VInx 1) B0))
        ,("tail", Right (TVec (VApp (VInx 1) B0) (VNum $ nVar (VInx 0))))
        ]
       ))
     ,(plain "cons"
      ,([VPVar, VPCon (plain "nil") []]
       ,[("value", Right (VApp (VInx 0) B0))
        ]
       ))
     ,(plain "cons"
      ,([VPVar, VPVar]
       ,[("head", Right (VApp (VInx 1) B0))
       ,("tail", Right (VApp (VInx 0) B0))
        ]
       ))
     ])
  ,(plain "snoc", M.fromList
     [(plain "List"
      ,([VPVar]
       ,[("tail", Right (TList (VApp (VInx 0) B0)))
        ,("head", Right (VApp (VInx 0) B0))
        ]))
     ,(plain "Vec"
      ,([VPVar, VPNum (NP1Plus NPVar)]
       ,[("tail", Right (TVec (VApp (VInx 1) B0) (VNum $ nVar (VInx 0))))
        ,("head", Right (VApp (VInx 1) B0))
        ]
       ))
     ])
  ,(plain "none", M.fromList
     [(plain "Option", ([VPVar], []))])
  ,(plain "some", M.fromList
     [(plain "Option", ([VPVar], [("value", Right (VApp (VInx 0) B0))]))])
  ,(plain "true", M.fromList [(plain "Bool", ([], []))])
  ,(plain "false", M.fromList [(plain "Bool", ([], []))])
  ]

defaultTypeConstructors :: M.Map UserName TypeKind
defaultTypeConstructors = M.fromList
  [(plain "Option", Star [("value", Star [])])
  ,(plain "List",   Star [("listValue", Star [])])
  ,(plain "Vec",    Star [("X", Star []), ("n", Nat)])
  ,(plain "Bool",   Star [])
  ,(plain "Bit",    Star [])
  ,(plain "Int",    Star [])
  ,(plain "Float",  Star [])
  ,(plain "String", Star [])
  ,(plain "Nat",    Star [])
  ,(plain "nil",    Star [])
  ,(plain "cons",   Star [("head", Star []), ("tail", Star [])])
  ]

{-
-- TODO: Make type aliases more flexible. Allow different patterns and allow Nat
-- kinds. Allow port pulling when applying them
-- TODO: Aliases for kernel types
typeAliases :: M.Map UserName (Modey m, [ValPat], BinderType m)
typeAliases = M.empty
{- Here is an example, for `type Vec5(X) = Vec(X, n)`:
M.fromList $
  [(plain "Vec5", (Braty, [VPVar], Con (plain "Vec") (VInx 0 :|: (Simple (Num 5)))))]

-- TODO: There's no way to parse the above syntax as:
  [(plain "Vec5", (Kerny, [VPVar], Of (VInx 0) (Simple (Num 5))))]
-}
-}

natConstructors :: M.Map UserName (Maybe NumPat, NumValue -> NumValue)
natConstructors = M.fromList
  [(plain "succ", (Just (NP1Plus NPVar)
                  ,nPlus 1))
  ,(plain "doub", (Just (NP2Times NPVar)
                  ,n2PowTimes 1))
  ,(plain "full", (Nothing, nFull))
  ,(plain "zero", (Just NP0
                  ,id))
  ]
