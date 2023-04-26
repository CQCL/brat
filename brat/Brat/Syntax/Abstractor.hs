{-# LANGUAGE PatternSynonyms #-}

module Brat.Syntax.Abstractor where

import Brat.Syntax.Port
import Brat.Syntax.Simple
import Brat.UserName

-- Ways to bind one thing
data Pattern
 = Bind String
 | PCon UserName Abstractor
 | Lit SimpleTerm
 | DontCare
 deriving Eq

instance Show Pattern where
  show (Bind x) = x
  show (PCon c AEmpty) = show c
  show (PCon c arg) = case patList (PCon c arg) of
    Just xs -> show xs
    Nothing -> show c ++ "(" ++ show arg ++ ")"
   where
    patList :: Pattern -> Maybe [Pattern]
    patList (PCons x xs) = (x:) <$> patList xs
    patList PNil = Just []
    patList _ = Nothing
  show (Lit tm) = show tm
  show DontCare = "_"

pattern PNone, PNil, PZero :: Pattern
pattern PNone = PCon (PrefixName [] "none") AEmpty
pattern PNil  = PCon (PrefixName [] "nil")  AEmpty
pattern PZero = PCon (PrefixName [] "zero") AEmpty

pattern PSome, POnePlus, PTwoTimes :: Pattern -> Pattern
pattern PSome x     = PCon (PrefixName [] "some") (APat x)
pattern POnePlus x  = PCon (PrefixName [] "succ") (APat x)
pattern PTwoTimes x = PCon (PrefixName [] "doub") (APat x)

pattern PCons :: Pattern -> Pattern -> Pattern
pattern PCons x xs  = PCon (PrefixName [] "cons") (APat x :||: APat xs)

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

newtype NormalisedAbstractor = NA Abstractor

instance Show NormalisedAbstractor where
  show (NA a) = show a

-- Concatenate normalised abstractors, making them right nested
cat :: NormalisedAbstractor -> NormalisedAbstractor -> NormalisedAbstractor
cat (NA a) (NA b) = NA $ aux a b
 where
  aux AEmpty b = b
  aux a AEmpty = a
  aux (a :||: b) c = a :||: aux b c
  aux a b = a :||: b

normaliseAbstractor :: Abstractor -> NormalisedAbstractor
normaliseAbstractor (a :||: b) = cat (normaliseAbstractor a) (normaliseAbstractor b)
normaliseAbstractor (APat p) = NA $ APat (normalisePatterns p)
 where
  normalisePatterns :: Pattern -> Pattern
  normalisePatterns (POnePlus a) = case normalisePatterns a of
    Lit (Num n) -> Lit (Num (n + 1))
    a -> POnePlus a
  normalisePatterns (PTwoTimes a) = case normalisePatterns a of
    Lit (Num n) -> Lit (Num (2 * n))
    a -> PTwoTimes a
  normalisePatterns (PCon c abs)
    = let (NA arg) = normaliseAbstractor abs in
        PCon c arg
  normalisePatterns x = x
normaliseAbstractor (APull ps abs) = let NA abs' = normaliseAbstractor abs in
                                       NA (APull ps abs')
normaliseAbstractor AEmpty = NA AEmpty

unNA :: NormalisedAbstractor -> Abstractor
unNA (NA a) = a
