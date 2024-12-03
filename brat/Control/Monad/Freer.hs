module Control.Monad.Freer (Free(..), req) where

import Control.Monad ((>=>))
import Data.Kind (Type)

data Free (sig :: Type -> Type) (v :: Type) where
  Ret :: v -> Free sig v
  Req ::  sig t -> (t -> Free sig v) -> Free sig v

instance Functor (Free sig) where
  fmap f (Ret v) = Ret (f v)
  fmap f (Req sig k) = Req sig (fmap f . k)

instance Applicative (Free sig) where
  pure = Ret
  (Ret f) <*> ma = fmap f ma
  (Req sig k) <*> ma = Req sig ((<*> ma) . k)

instance Monad (Free sig) where
  Ret v >>= k = k v
  Req r j >>= k = Req r (j >=> k)

req :: sig t -> Free sig t
req s = Req s Ret
