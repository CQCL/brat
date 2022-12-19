{-# LANGUAGE PatternSynonyms #-}

module Brat.Syntax.Abstractor where

import Brat.Syntax.Port
import Brat.Syntax.Simple

-- Ways to bind one thing
data Pattern
 = Bind String
 | PCon String Abstractor
 | Lit SimpleTerm
 | DontCare
 deriving Eq

instance Show Pattern where
  show (Bind x) = x
  show (PCon c AEmpty) = c
  show (PCon c arg) = case patList (PCon c arg) of
    Just xs -> show xs
    Nothing -> c ++ "(" ++ show arg ++ ")"
   where
    patList :: Pattern -> Maybe [Pattern]
    patList (PCons x xs) = (x:) <$> patList xs
    patList PNil = Just []
    patList _ = Nothing
  show (Lit tm) = show tm
  show DontCare = "_"

pattern PNone, PNil :: Pattern
pattern PNone       = PCon "none" AEmpty
pattern PNil        = PCon "nil"  AEmpty

pattern PSome, POnePlus, PTwoTimes :: Pattern -> Pattern
pattern PSome x     = PCon "some" (APat x)
pattern POnePlus x  = PCon "succ" (APat x)
pattern PTwoTimes x = PCon "doub" (APat x)

pattern PCons :: Pattern -> Pattern -> Pattern
pattern PCons x xs  = PCon "cons" (APat x :||: APat xs)

-- Ways to bind a row of things
data Abstractor
 -- There's nothing and that's how we want it
 = AEmpty
 | Abstractor :||: Abstractor
 -- Pull port name being abstracted to the front
 -- b:x, c:y, z -> ...
 | APull [PortName] (Abstractor)
 | APat Pattern
 deriving Eq

instance Show (Abstractor) where
  show AEmpty = "<empty>"
  show (x :||: y) = show x ++ ", " ++ show y
  show (APull ps abs) = concat ((++":") <$> ps) ++ show abs
  show (APat p) = show p

occursInAbstractor :: String -> Abstractor -> Bool
occursInAbstractor _ AEmpty = False
occursInAbstractor s (a :||: b) = occursInAbstractor s a || occursInAbstractor s b
occursInAbstractor s (APull _ a) = occursInAbstractor s a
occursInAbstractor s (APat p) = occursInPat s p
 where
  occursInPat _ (Lit _) = False
  occursInPat x (Bind y) = x == y
  occursInPat s (PCon _ xs) = occursInAbstractor s xs
  occursInPat _ DontCare = False
