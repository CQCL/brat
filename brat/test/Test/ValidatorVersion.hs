module Test.ValidatorVersion where

import Data.Bifunctor (first)
import Data.Char (isDigit)
import Data.List (isPrefixOf)

newtype Version = Version (Int, Int, Int) deriving Eq

instance Show Version where
  show (Version (maj,min,patch)) = show maj ++ "." ++ show min ++ "." ++ show patch

data ValidatorStatus = Good | NotInPath | BadVersion Version | MalformedOutput String

parseValidatorVersion :: String -> Maybe Version
parseValidatorVersion cs
 | prefix `isPrefixOf` cs = parseVersion (drop (length prefix) cs)
 | otherwise = Nothing
 where
  prefix = "hugr_validator "

parseNum :: String -> Maybe (Int, String)
parseNum = fmap (first read) . parseNumStr

parseNumStr :: String -> Maybe (String, String)
parseNumStr (c:cs) | isDigit c = case parseNumStr cs of
  Just (ds, cs) -> Just (c:ds, cs)
  Nothing -> Just ([c], cs)
parseNumStr _ = Nothing

parsePoint :: String -> Maybe ((), String)
parsePoint ('.':cs) = Just ((), cs)
parsePoint _ = Nothing

parseVersion cs = do
  (maj, rest) <- parseNum cs
  ((), rest) <- parsePoint rest
  (min, rest) <- parseNum rest
  ((), rest) <- parsePoint rest
  (patch, rest) <- parseNum rest
  pure (Version (maj, min, patch))
