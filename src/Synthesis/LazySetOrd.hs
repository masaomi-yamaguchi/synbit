{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wunused-imports #-}

module Synthesis.LazySetOrd
    ( Set
    , empty
    , singleton
    , add
    , addAll
    , select
    , contains) where

import           Control.Monad.Sharing
import           Prelude hiding (lookup)
import qualified Control.Applicative as A
import           Control.Monad (MonadPlus, mzero)

data Set m a = Nil
             | Cons Bool a (m (Set m a))

instance (Monad m, Shareable m a) => Shareable m (Set m a) where
  shareArgs _ Nil = return Nil
  shareArgs f (Cons isShared v xs)
    | isShared = return $ Cons True v xs
  shareArgs f (Cons isShared a xs)
    | otherwise = do
      xs' <- f xs
      return $ Cons True a xs'

nil :: Monad m => m (Set m a)
nil = return Nil

cons :: Monad m => a -> m (Set m a) -> m (Set m a)
cons v env = return $ Cons False v env

empty :: Monad m => m (Set m a)
empty = nil

singleton :: Monad m => a -> m (Set m a)
singleton a = cons a empty

-- mxsがshare済みであることを仮定
add :: (Monad m, Ord a) => a -> m (Set m a) -> m (Set m a)
add x mxs = do
  xs <- mxs
  case xs of
    Nil           -> cons x nil
    Cons _ k rest -> do
      if k == x
        then cons x rest
        else if k > x
             then cons x (cons k rest)
             else cons k (add x rest)

addAll :: (Monad m, Ord a) => m (Set m a) -> m (Set m a) -> m (Set m a)
addAll mbind env = do
  bind <- mbind
  case bind of
    Nil           -> env
    Cons _ k rest -> do
      add k (addAll rest env)

foldrS :: Monad m => (a -> m b -> m b) -> m b -> m (Set m a) -> m b
foldrS f e ml = do
  l <- ml
  case l of
    Nil         -> e
    Cons _ k xs -> f k (foldrS f e xs)

select :: (MonadPlus m) => m (Set m a) -> m a
select env = foldrS (\a b -> (return a) A.<|> b) mzero env

contains :: (Monad m, Ord a) => a -> m (Set m a) -> m Bool
contains x mxs = do
  xs <- mxs
  case xs of
    Nil           -> return False
    Cons _ k rest -> do
      if k == x
        then return True
        else if k > x
             then return False
             else contains x rest
