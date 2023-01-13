{-# LANGUAGE DataKinds, GADTs #-}

module Brat.LSP.Find (Context(..), getInfo) where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (catMaybes)

import Brat.FC
import Brat.LSP.State
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.Syntax.Skel

data Context
  = Context { declName :: String
            , root :: Skel
            -- May be nothing if not hovering over a term
            , thing :: Skel
            , runtime :: Runtime
            } deriving (Eq, Show)

getInfo :: ProgramState -> Pos -> Maybe Context
getInfo ps pos
  = case filter pred (decls ps) of
      [] -> Nothing
      (x:_) -> buildContext pos x
 where
  pred :: Decl' io raw -> Bool
  pred Decl{..} = pos `inside` fnLoc

  buildContext :: Pos -> Decl' io (FunBody Term Noun) -> Maybe Context
  buildContext pos Decl{..} = do
    body <- findInBody pos fnBody
    subject <- getThing pos body
    pure $ Context { declName = fnName
                   , root = unWC body
                   , thing = subject
                   , runtime = fnRT
                   }

  findInBody :: Juxt k => Pos -> FunBody Term k -> Maybe (WC Skel)
  findInBody pos (NoLhs (WC fc rhs))
    | pos `inside` fc = Just (WC fc (stripInfo rhs))
  -- TODO: Doesn't search in LHS
  findInBody pos (Clauses (c :| cs)) = findInClauses (c:cs)
   where
    findInClauses :: [(WC Abstractor, WC (Term Chk Noun))] -> Maybe (WC Skel)
    findInClauses [] = Nothing
    findInClauses ((_, rhs):cs)
     | rfc <- fcOf rhs, pos `inside` rfc = Just (stripInfo <$> rhs)
     | otherwise = findInClauses cs
  findInBody _ _ = Nothing

  getThing :: Pos -> WC Skel -> Maybe Skel
  getThing pos (WC fc x)
    | pos `inside` fc = case catMaybes (getThing pos <$> subTerms x) of
                          [] -> Just x
                          -- xs should be the empty list, but I don't think it's
                          -- worth crashing the server over
                          (x:_) -> Just x
    | otherwise = Nothing
