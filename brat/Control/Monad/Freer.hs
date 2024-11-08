module Control.Monad.Freer where

import Control.Monad ((>=>))
import Data.Kind (Type)
import qualified Data.Map as M
import qualified Data.Set as S

import Brat.Syntax.Port

-- A mapping of metavars to metavars, for a single problem:
--  * e -> Unstuck means e has been solved
--  * e -> Awaiting es means the problem's been transferred
--  * e not in news means no change to e
newtype News = News (M.Map End Stuck)

updateEnd :: News -> End -> Stuck
updateEnd (News m) e = case M.lookup e m of
  Nothing ->  AwaitingAny (S.singleton e)
  Just s -> s

-- The RHS of the operation is the newer news
-- Invariant: The domains of these Newses are disjoint
instance Semigroup News where
  (News m1) <> n2@(News m2) = News (m2 `M.union` (M.map (/// n2) m1))

instance Monoid News where
  mempty = News M.empty

data Stuck
 = Unstuck
 | AwaitingAny (S.Set End)
 deriving Show

instance Semigroup Stuck where
  (AwaitingAny es1) <> (AwaitingAny es2) = AwaitingAny (S.union es1 es2)
  _ <> _ = Unstuck

instance Monoid Stuck where
  mempty = AwaitingAny S.empty

data Free (sig :: Type -> Type) (v :: Type) where
  Ret :: v -> Free sig v
  Req ::  sig t -> (t -> Free sig v) -> Free sig v

instance Functor (Free sig) where
  fmap f (Ret v) = Ret (f v)
  fmap f (Req sig k) = Req sig (fmap f . k)

class NewsWatcher t where
  (///) :: t -> News -> t

instance NewsWatcher Stuck where
  Unstuck /// _ = Unstuck
  (AwaitingAny es) /// n = foldMap (updateEnd n) es

instance NewsWatcher (News -> t) where
  f /// n = f . (n <>)

instance NewsWatcher (Free sig v) where
  Ret v /// _ = Ret v
  Req sig k /// n = Req sig $ \v -> k v /// n

instance Applicative (Free sig) where
  pure = Ret
  (Ret f) <*> ma = fmap f ma
  (Req sig k) <*> ma = Req sig ((<*> ma) . k)

instance Monad (Free sig) where
  Ret v >>= k = k v
  Req r j >>= k = Req r (j >=> k)

req :: sig t -> Free sig t
req s = Req s Ret
