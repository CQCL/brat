module Brat.Compile.Scheme (compileFile) where

import Brat.FC
import Brat.Syntax.Skel
import Brat.Syntax.Core
import Brat.Syntax.Common hiding (List)

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Functor ((<&>))
import Data.List.NonEmpty (nonEmpty, NonEmpty(..))
import Data.Maybe (fromJust)

import Debug.Trace

type M = Reader [(String, Int)]

indent :: String -> String
indent = unlines . fmap (' ':) . lines

mangle :: String -> String
mangle = undefined

singleton :: a -> [a]
singleton x = [x]

data SExp
  = SExp :@ [SExp]
  | Prim String
  | ScmVar String
  | SLit SimpleTerm
  | Lambda [String] [SExp]
  | List [SExp]
  | Define String SExp
  | Match [(SExp, SExp)]
  | Atom String
 deriving Show

append a b = Prim "append" :@ [a, b]
stake a b = Prim "take" :@ [a, b]
sdrop a b = Prim "take" :@ [a, b]
cons a b = Prim "cons" :@ [a, b]

($$) :: SExp -> SExp -> SExp
f $$ a = Prim "apply" :@ [f, a]

scheme :: Skel -> M SExp
scheme (SSimple t) = pure $ SLit t
scheme (SPair a b) = cons <$> scheme (unWC a) <*> scheme (unWC b)
scheme (SHole h) = error $ "Found hole while scheming: " ++ h
scheme (SJuxtNoun a b) = List <$> mapM (scheme . unWC) [a,b]
scheme (SJuxtVerb a b) = do
  i <- arity (unWC a)
  j <- arity (unWC b)
  a <- scheme (unWC a)
  b <- scheme (unWC b)
  pure $ Lambda ["args"] [append (a $$ stake (SLit (Num i)) (ScmVar "args")) (b $$ sdrop (SLit (Num j)) (ScmVar "args"))]
scheme (STh f) = Lambda [] . singleton <$> scheme (unWC f)
-- scheme Pull     :: [Port] -> WC (Term Chk k) -> Term Chk k
--scheme Var      :: String -> Term Syn Noun  -- Look up in noun (value) env
--scheme Bound    :: Int -> Term Syn Noun  -- Look up in noun (value) env
scheme (SVar s) = pure $ ScmVar s
scheme (SApp fun arg)
  | SJuxtNoun _ _ <- unWC arg = ($$) <$> scheme (unWC fun) <*> scheme (unWC arg)
  | otherwise = ($$) <$> scheme (unWC fun) <*> (List . singleton <$> scheme (unWC arg))
scheme (SAnn tm _) = scheme (unWC tm)
scheme (SDo f) = scheme (unWC f) <&> (:@ [])
-- scheme (:-:)    :: WC (Term Syn k) -> WC (Term d Verb) -> Term d k -- vertical juxtaposition (diagrammatic composition)
scheme (SLam abst body) = Lambda (aux abst) . singleton <$> scheme (unWC body)
 where
  aux :: Abstractor -> [String]
  aux (Bind x) = [x]
  aux (x :||: y) = aux x ++ aux y
  aux (APull _ _) = error "apull"
scheme (SVec xs) = List <$> mapM (scheme.unWC) xs
--scheme Slice    :: WC (Term Chk Noun) -> Slice (WC (Term Chk Noun)) -> Term Chk Noun
--scheme Select   :: WC (Term Syn Noun) -> WC (Term Chk Noun) -> Term Chk Noun
--scheme Thin     :: WC (Term Chk Noun) -> Term Syn Noun
scheme x = error $ "unimplemented: scheme " ++ show x

data Abs = ABind String | APat (Pattern Abs) | ALit SimpleTerm

schemeClause :: NonEmpty (Abstractor, Skel) -> M SExp
schemeClause (x@(a,_) :| xs) = do
  branches <- mapM branch (x:xs)
  pure (Match branches)
 where
  vars = singleton.(['A'..'z']!!) <$> [0..arity a - 1]

  branch :: (Abstractor, Skel) -> M (SExp, SExp)
  branch (a, s) = scheme s <&> (www $ abstList a,)

  www :: [Abs] -> SExp
  www (x:xs) = wee x :@ (wee <$> xs)

  wee :: Abs -> SExp
  wee (ABind x) = ScmVar x
  wee (APat PNil) = Atom "Nil"
  wee (APat (PCons a b)) = Atom "Cons" :@ [wee a, wee b]
--  wee (APat (POnePlus 
  wee (ALit x) = SLit x

  abstList :: Abstractor -> [Abs]
  abstList (a :||: b) = abstList a ++ abstList b
  abstList (Bind x) = [ABind x]
  abstList (Pat p) = [APat (head . abstList <$> p)]
  abstList (Lit tm) = [ALit tm]
  abstList (VecLit tm) = concatMap abstList tm

  arity :: Abstractor -> Int
  arity (a :||: b) = arity a + arity b
  arity (APull _ a) = arity a
  arity _ = 1
bracket :: String -> String
bracket s = '(' : s ++ ")"

toString :: SExp -> String
toString (f :@ args) = bracket . unwords $ toString <$> (f:args)
toString (Prim s) = s
toString (ScmVar s) = s
toString (SLit (Num n)) = show n
toString (SLit (Bool b)) = if b then "'t" else "'()"
toString (SLit (Text s)) = show s
toString (SLit (Float s)) = show s
toString (SLit Unit) = "'Unit"
toString (Lambda vars body) = bracket $
  unlines (("lambda" ++ bracket (unwords vars)):((indent.toString) <$> body))
toString (List []) = "'()"
toString (List xs) = toString $ Prim "list" :@ xs
toString (Define name body) = bracket $
  unlines [unwords ["define",name]
          ,indent $ toString body]
toString (Match branches) = bracket $ unlines ("case-lambda":(indent.branch<$>branches))
 where
  branch :: (SExp, SExp) -> String
  branch (p, s) = '[':toString p ++ " " ++ toString s ++ "]"
toString (Atom a) = '\'':a

compileFile :: ([NDecl], [VDecl]) -> String
compileFile (nds, vds) = flip runReader cenv $ do
  nds <- mapM compileNDecl nds
  vds <- mapM compileVDecl vds
  pure $ unlines (prelude:vds ++ nds ++ ["(main)"])
 where
  todo = pure $ Prim "'todo"

  cenv = vds <&> \decl -> case fnSig decl of
                            (ss :-> ts) -> (fnName decl, length ss)


  compileNDecl :: NDecl -> M String
  compileNDecl Decl {..}
   | Extern _ <- fnLocality = pure ""
   | otherwise = toString . Define fnName <$>
    case fnBody of
      [NounBody body] -> scheme (stripInfo (unWC body))
      other -> todo

  compileVDecl :: VDecl -> M String
  compileVDecl Decl {..}
   | Extern _ <- fnLocality = pure ""
   | otherwise = toString . Define fnName <$>
    case fnBody of
      [NoLhs rhs] -> todo
      (x@(Clause _ _):xs) -> schemeClause (clause x :| (clause <$> xs))
      cs -> trace ("cs: " ++ fnName ++ " " ++ show cs) undefined
   where
    clause :: Clause Term Verb -> (Abstractor, Skel)
    clause (Clause lhs rhs) = (unWC lhs, stripInfo (unWC rhs))

{-
  compileVDecl Decl {..} = case fnBody of
                            NoLhs rhs -> toString . Define fnName <$> scheme (stripInfo (unWC rhs))
                            Clause lhs rhs -> pure "" -- pure $ toString (Prim fnName)
-}

-- input arity
arity :: Skel -> Reader [(String, Int)] Int
arity (SSimple _) = pure 0
arity (SPair _ _) = pure 0
arity (SHole _)   = pure 0
arity (SJuxtVerb a b) = (+) <$> arity (unWC a) <*> arity (unWC b)
arity (SJuxtNoun a b) = (+) <$> arity (unWC a) <*> arity (unWC b)
arity (STh th) = arity (unWC th)
arity (SPull _ x) = arity (unWC x)
arity (SVar _) = pure 0
arity (SBound _) = undefined
arity (SApp f a) = pure 0
arity (SAnn tm _) = arity (unWC tm)
arity (SDo x) = arity (unWC x)
arity (SComp a b) = arity (unWC a)
arity (SLam abst _) = pure $ abstArity abst
 where
  abstArity (Bind _) = 1
  abstArity (a :||: b) = abstArity a + abstArity b
  abstArity (APull _ x) = abstArity x
arity (SVec _) = pure 0

prelude = unlines
 ["(import (chezscheme))"
 ,""
 ,"(define take"
 ," (lambda (n xs)"
 ,"  (if (positive? n)"
 ,"      (cons (car xs) (take (- n 1) (cdr xs)))"
 ,"      ('()))))"
 ,""
 ,"(define drop"
 ," (lambda (n xs)"
 ,"  (if (positive? n)"
 ,"      (drop (- n 1) (cdr xs))"
 ,"      xs)))"
 ,""
 ,"(define brat-list"
 ,"  (lambda (xs)"
 ,"    (if (null? xs)"
 ,"        (list 'Nil)"
 ,"        (list 'Cons (car xs) (brat-list (cdr xs))))))"
 ,""
 ,"(define ls"
 ," (lambda (dir)"
 ,"  (brat-list (directory-list dir))))"
 ,""
 ]
