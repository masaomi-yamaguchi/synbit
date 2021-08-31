{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}

module Control.Monad.Enumerate
  (
    LWS, Matrix, Enumerate, printResults,
    module Control.Applicative
  ) where

import           Control.Applicative   (Alternative (..))
import           Control.Delay
import           Control.Gen
import           Control.Monad         (ap)
import           Data.Coerce
import           Data.Foldable         (asum, toList)

import qualified Data.IntMap.Strict    as I

import           Control.Monad.State
import           Text.Show             (showListWith)
import           Unsafe.Coerce

import           Control.Monad.Sharing

type Stream a = [a]

newtype LWS f a = LWS { parts :: Stream (f a) } deriving (Functor, Show)
-- | A monad inspired by Spivey's "Combiantors for Breadth-First
-- Search". But, of which Applicative instance is inspired by Duregård
-- et al.'s "Feat: Functional Enumeration of Algebraic Types".
--
-- An intuition underlying the data is that the ith element of the
-- outer stream represents elements in the ith level in the search
-- tree, which are supposed to be finite.


printResults :: Show (f a) => LWS f a -> IO ()
printResults = go 0 . parts
  where
    go _ [] = putStrLn "\n -- End."
    go n (x:xs) = do
      let s = "-- Generation: " ++ show n ++ " "
      putStrLn $ s ++ take (80 - length s) (repeat '-')
      print x
      go (n+1) xs


instance Alternative f => Applicative (LWS f) where
  pure  a = LWS [pure a]  -- meaning that a has cost a.

  -- [a0, a1, a2, a3,...] <*> [b0, b1, b2, b3, ...]
  -- = [a0 <*> b0, a1 <*> b0 <|> a0 <*> b1 , a0 <*> b2 <|> a1 <*> b1 <|> a2 <*> b0, ...]
  LWS s1 <*> LWS s2 = LWS $ map (conv s1) (reversals s2)
    where
      -- conv [a0, a1, a2, a3, ...] [b2, b1, b0] = a0 <*> b2 <|> a1 <*> b1 <|> a2 <*> b0
      conv :: Alternative f => [f (a -> b)] -> [f a] -> f b
      conv xs ys = asum (zipWith (<*>) xs ys)

      -- reversals [1,2,3] = [[1], [2,1], [3,2,1]]
      reversals :: [a] -> [[a]]
      reversals = go []
        where
          go _ [] = []
          go rev (x:xs) = let rev' = x:rev
                          in rev' : go rev' xs

merge :: Alternative f => Stream (f a) -> Stream (f a) -> Stream (f a)
merge [] ys         = ys
merge (x:xs) []     = x:xs
merge (x:xs) (y:ys) = (x <|> y) : merge xs ys

instance Alternative f => Alternative (LWS f) where
  empty = LWS empty
  {-# INLINABLE empty #-}

  LWS s1 <|> LWS s2 = LWS (merge s1 s2)
  {-# INLINABLE (<|>) #-}

instance (Foldable f, Alternative f) => MonadPlus (LWS f) where


diag :: Alternative f => Stream (Stream (f a)) -> Stream (f a)
diag []           = []
diag ([]:xss)     = empty:diag xss
diag ((x:xs):xss) = x:merge xs (diag xss)

instance (Foldable f, Alternative f) => Monad (LWS f) where
  return = pure
  {-# INLINE return #-}

  -- To define m >>= f, first we map f to each inner elements.
  -- After that, we obtain a data like:
  --
  -- s = [ { [{1,2,3}, {23}, ... ], ... }, {  [{4,5,6}, ... ] , ... } , ... ] :: Stream [ Stream [ a ] ]
  --
  -- First, we combine the inner streams to obtain Steam (Stream [a]), which can be done by
  --
  --   foldr (<|>) empty
  --
  -- assuming that LWS is an alternative instance

  --
  -- To flatten such data, an important thing here is that jth element
  -- is the inner stream located in the ith element in the outer
  -- stream should go to (i + j) th elements after flattening.
  --
  LWS m >>= f =
    LWS $ diag $ map (foldr ((<|>) . coerce . f) empty) m


instance Foldable f => Foldable (LWS f) where
  foldr c n (LWS s) = foldr (\a r  -> foldr c r a) n s

instance Alternative f => Semigroup (LWS f a) where
  (<>) = (<|>)

instance Alternative f => Monoid (LWS f a) where
  mempty = empty


instance Alternative f => Gen (LWS f a) where
  cost n (LWS st) = LWS (replicate n empty ++ st)

instance Alternative f => Delay (LWS f) where
  delay n (LWS st) = LWS (replicate n empty ++ st)

type Matrix = LWS []

type Enumerate = LWS Fin

data Fin a = Fin { card :: {-# UNPACK #-} !Int, index :: !(Int -> a) } deriving Functor

instance Show a => Show (Fin a) where
  showsPrec _ xs = showListWith shows (Data.Foldable.toList xs)

instance Applicative Fin where
  pure a = Fin 1 (const a)
  Fin n f <*> Fin m g = Fin (n * m) $ \k ->
    let (!i, !j) = divMod k n
    in f i (g j)

instance Alternative Fin where
  empty = Fin 0 (\_ -> undefined)
  Fin n f <|> Fin m g = Fin (n + m) $ \k ->
    if k < n then f k else g $! (k - n)

instance Foldable Fin where
  foldr c n (Fin len f) = go 0
    where
      go i | i == len  = n
           | otherwise = f i `c` go (i + 1)


-- data Untyped = forall a. Untyped a
-- coer :: Untyped -> a
-- coer (Untyped a) = unsafeCoerce a
-- data Store = Store { namesource :: !Int, table :: !(I.IntMap Untyped) }

-- -- direct style
-- newtype LazyD f a = LazyD { runLazyD :: StateT Store f a }
--   deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadState Store)

-- instance MonadPlus f => Sharing (LazyD f) where
--   share a = memo (a >>= shareArgs share)

-- instance Delay f => Delay (LazyD f) where
--   delay weight (LazyD m) = LazyD $ StateT $ \s -> delay weight (runStateT m s)

-- memo :: Monad f => LazyD f a -> LazyD f (LazyD f a)
-- memo m = do
--   store <- get
--   let idx = namesource store
--   put (store { namesource = idx + 1})
--   return $ do
--     store <- get
--     case I.lookup idx $ table store of
--       Just v  -> return (coer v)
--       Nothing -> do
--         v <- m
--         put (store { table = I.insert idx (Untyped v) $ table store})
--         return v

-- collectD :: (MonadPlus f, Delay f) => (forall s. (Sharing s, Delay s) => s a) -> f a
-- collectD (LazyD m) = evalStateT m (Store 0 I.empty)
