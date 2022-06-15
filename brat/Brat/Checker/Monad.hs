module Brat.Checker.Monad where

import Brat.Checker.Quantity (Quantity(..), qpred)
import Brat.Checker.Types
import Brat.Error (Error(..), ErrorMsg(..))
import Brat.FC (FC)
import Brat.Graph (Node'(..), Src, Thing(..), Tgt)
import Brat.Naming (fresh, Name, Namespace)
import Brat.Syntax.Common
import Brat.Syntax.Core (Decl, Input, Output, SType, VType, Term)
import Brat.UserName (UserName)

import Control.Monad.Freer

import Control.Monad.Fail ()
import Data.List (intercalate)
import qualified Data.Map as M

data Context = Ctx { venv :: VEnv
                   , decls :: [Decl]
                   , typeFC :: FC
                   }

data CheckingSig ty where
  Fresh   :: String -> CheckingSig Name
  Throw   :: Error  -> CheckingSig a
  LogHole :: TypedHole -> CheckingSig ()
  AskFC   :: CheckingSig FC
  VLup    :: UserName -> CheckingSig (Maybe [(Src, VType)])
  KLup    :: UserName -> CheckingSig (Maybe (Src, SType))
  Node    :: Name -> Node -> CheckingSig ()
  Wire    :: Wire -> CheckingSig ()
  Decls   :: CheckingSig [Decl]
  KDone   :: CheckingSig ()
  AskVEnv :: CheckingSig VEnv

localFC :: FC -> Checking v -> Checking v
localFC _ (Ret v) = Ret v
localFC f (Req AskFC k) = localFC f (k f)
localFC f (Req r k) = Req r (localFC f . k)

localVEnv :: VEnv -> Checking v -> Checking v
localVEnv _   (Ret v) = Ret v
localVEnv ext (Req (VLup x) k) | Just x <- M.lookup x ext = localVEnv ext (k (Just x))
localVEnv ext (Req AskVEnv k) = do env <- req AskVEnv
                                   localVEnv ext (k (M.union ext env)) -- ext shadows env
localVEnv ext (Req r k) = Req r (localVEnv ext . k)

wrapError :: (Error -> Error) -> Checking v -> Checking v
wrapError _ (Ret v) = Ret v
wrapError f (Req (Throw e) k) = Req (Throw (f e)) k
wrapError f (Req r k) = Req r (wrapError f . k)

vlup :: UserName -> Checking [(Src, VType)]
vlup s = do
  req (VLup s) >>= \case
    Just vty -> pure vty
    Nothing -> err $ VarNotFound (show s)

lookupAndUse :: UserName -> KEnv -> Either Error (Maybe ((Src, SType), KEnv))
lookupAndUse x kenv = case M.lookup x kenv of
   Nothing -> Right Nothing
   Just (q, rest) -> case qpred q of
                      Nothing -> Left $ Err Nothing Nothing $ TypeErr $ (show x) ++ " has already been used"
                      Just q -> Right $ Just (rest, M.insert x (q, rest) kenv)

localKVar :: KEnv -> Free CheckingSig v -> Free CheckingSig v
localKVar _   (Ret v) = Ret v
localKVar env (Req (KLup x) k) = case lookupAndUse x env of
                                   Left err@(Err (Just _) _ _) -> req $ Throw err
                                   Left (Err Nothing _ msg) -> err msg
                                   Right (Just (th, env)) -> localKVar env (k (Just th))
                                   Right Nothing -> Req (KLup x) (localKVar env . k)
localKVar env (Req KDone k) = case [ x | (x,(One,_)) <- M.assocs env ] of
                                [] -> (localKVar env . k) ()
                                xs -> typeErr $
                                      unwords ["Variable(s)"
                                              ,intercalate ", " (fmap show xs)
                                              ,"haven't been used"
                                              ]
localKVar env (Req r k) = Req r (localKVar env . k)

handler :: Free CheckingSig v
        -> Context
        -> Namespace
        -> Either Error (v,([TypedHole],Graph),Namespace)
handler (Ret v) _ ns = return (v, mempty, ns)
handler (Req s k) ctx ns
  = case s of
      Fresh str -> let (name, root) = fresh str ns in
                     handler (k name) ctx root
      Throw err -> Left err
      LogHole hole -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                         return (v,(hole:holes,g),ns)
      AskFC -> handler (k (typeFC ctx)) ctx ns
      VLup s -> handler (k $ M.lookup s (venv ctx)) ctx ns
      Node name node -> do
        (v,(holes,g),ns) <- handler (k ()) ctx ns
        return (v,(holes,(M.singleton name node, []) <> g),ns)
      Wire w -> do (v,(holes,g),ns) <- handler (k ()) ctx ns
                   return (v,(holes,(M.empty,[w]) <> g),ns)
      Decls ->  handler (k (decls ctx)) ctx ns
      -- We only get a KLup here if the variable has not been found in the kernel context
      KLup _ -> handler (k Nothing) ctx ns
      -- Receiving KDone may become possible when merging the two check functions
      KDone -> error "KDone in handler - this shouldn't happen"
      AskVEnv -> handler (k (venv ctx)) ctx ns

type Checking = Free CheckingSig

err :: ErrorMsg -> Checking a
err msg = do
  fc <- req AskFC
  req $ Throw $ Err (Just fc) Nothing msg

typeErr :: String -> Checking a
typeErr = err . TypeErr

-- This way we get file contexts when pattern matching fails
instance MonadFail Checking where
  fail = typeErr

next :: String -> Thing -> [Input] -> [Output] -> Checking Name
next str th ins outs = do
  this <- req (Fresh str)
  () <- req (Node this (BratNode th ins outs))
  pure this

knext :: String -> Thing -> [(Port, SType)] -> [(Port, SType)] -> Checking Name
knext str th ins outs = do
  this <- req (Fresh str)
  () <- req (Node this (KernelNode th ins outs))
  pure this

wire :: Wire -> Checking ()
wire w = req $ Wire w

class (Show t) => AType t where
  anext :: String -> Thing -> [(Port, t)] -> [(Port, t)] -> Checking Name
  makeVec :: t -> Term Chk Noun -> t
  bindToLit :: t -> Either String SimpleType -- Left is error description
  awire :: (Src, t, Tgt) -> Checking ()

instance AType SType where
  anext = knext
  makeVec = Of
  bindToLit Bit = Right Boolean
  bindToLit _ = Left " in a kernel"
  awire (src, ty, tgt) = req $ Wire (src, Left ty, tgt)

instance AType VType where
  anext = next
  makeVec = Vector
  bindToLit (SimpleTy ty) = Right ty
  bindToLit _ = Left ""
  awire (src, ty, tgt) = req $ Wire (src, Right ty, tgt)
