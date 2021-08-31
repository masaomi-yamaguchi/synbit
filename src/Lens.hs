module Lens where

import Control.Category
import Prelude hiding (id, (.))
import Data.Maybe (fromJust)
import RunTimeException
import Control.DeepSeq
import Control.Monad ((<=<))

import Err

-- partial lens 
newtype Lens a b =
  Lens { runLens :: a -> Err (b, b -> Err a) }

instance NFData (Lens a b) where
  rnf (Lens _) = ()

fromInj :: Inj a b -> Lens a b
fromInj (Inj f fi) =
  Lens $ \s -> return (f s, return . fi)

fromInjection :: (a -> b) -> (b -> a) -> Lens a b
fromInjection f g = fromInj $ Inj f g

fromGetPut :: (a -> b) -> (a -> b -> a) -> Lens a b
fromGetPut get put =
  Lens $ \s -> return (get s, return . put s)

fromPartialGetPut :: (a -> Err b) -> (a -> b -> Err a) -> Lens a b
fromPartialGetPut get put = Lens $ \s -> do
  v <- get s
  return (v, put s)

instance Category Lens where
  id = fromInj id
  (Lens f2) . (Lens f1) = Lens $ \s -> do
    (v1, r1) <- f1 s
    (v2, r2) <- f2 v1
    return (v2, r1 <=< r2)

get :: Lens a b -> a -> Err b
get (Lens f) s = fst <$> f s
put :: Lens a b -> a -> b -> Err a
put (Lens f) s v = (snd <$> f s) >>= \refl -> refl v

-- Partial injection
data Inj a b = Inj { fwd :: a -> b, bwd :: b -> a }

invert :: Inj a b -> Inj b a
invert (Inj f g) = Inj g f

instance Category Inj where
  id = Inj id id
  Inj f fi . Inj g gi = Inj (f . g) (gi . fi)
