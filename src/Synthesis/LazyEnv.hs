{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wunused-imports #-}

module Synthesis.LazyEnv
    ( Env
    , empty
    , singleton
    , lookup
    , insert
    , insertAll
    , insertAll'
    , lookup'
    , foldrE
    , toList
    , fromList
    , select
    , remove
    , map
    , all
    , any) where

import           Control.Monad.Sharing
import qualified Data.Monadic.List as L
import           Prelude hiding (lookup, map, any, all)
import qualified Control.Applicative as A
import           Control.Monad (MonadPlus, mzero)

data Env m a b = Nil
               | Cons Bool a (m b) (m (Env m a b))

instance (Monad m, Eq a, Shareable m b) => Shareable m (Env m a b) where
  shareArgs _ Nil = return Nil
  shareArgs f (Cons isShared k v xs)
    | isShared = return $ Cons True k v xs
  shareArgs f (Cons isShared k v xs)
    | otherwise = do
      v' <- f v
      xs' <- f xs
      return $ Cons True k v' xs'

nil :: Monad m => m (Env m a b)
nil = return Nil

cons :: Monad m => a -> m b -> m (Env m a b) -> m (Env m a b)
cons k v env = return $ Cons False k v env

empty :: Monad m => m (Env m a b)
empty = nil

singleton :: Monad m => a -> m b -> m (Env m a b)
singleton a b = cons a b empty

lookup :: (Monad m, Ord a) => a -> m (Env m a b) -> m (Maybe (m b))
lookup x menv = do
  env <- menv
  case env of
    Nil -> return Nothing
    Cons _ k v rest -> do
      if k == x
        then return (Just v)
        else if k > x
             then return Nothing
             else lookup x rest

mem :: (Monad m, Ord a) => a -> m (Env m a b) -> m Bool
mem x env = do
  look <- lookup x env
  case look of
    Just _  -> return True
    Nothing -> return False

insert :: (Monad m, Ord a) => a -> m b -> m (Env m a b) -> m (Env m a b)
insert x v menv = do
  env <- menv
  case env of
    Nil -> cons x v nil
    Cons _ k v' rest -> do
      if k == x
        then cons x v rest
        else if k > x
             then cons x v (cons k v' rest)
             else cons k v' (insert x v rest)

remove :: (Monad m, Ord a) => a -> m (Env m a b) -> m (Env m a b)
remove x menv = do
  env <- menv
  case env of
    Nil -> nil
    Cons _ k v' rest -> do
      if k == x
        then rest
        else if k > x
             then cons k v' rest
             else cons k v' (remove x rest)

insertAll
  :: (Monad m, Ord a) => m (Env m a b) -> m (Env m a b) -> m (Env m a b)
insertAll mbind env = do
  bind <- mbind
  case bind of
    Nil -> env
    Cons _ k v rest -> do
      insert k v (insertAll rest env)

insertAll' :: (Monad m, Ord a)
           => m (L.List m (a, m b))
           -> m (Env m a b)
           -> m (Env m a b)
insertAll' mbind env = do
  bind <- mbind
  case bind of
    L.Nil           -> env
    L.Cons mkv rest -> do
      (k, v) <- mkv
      insert k v (insertAll' rest env)

lookup' :: (Monad m, Ord a) => a -> m (L.List m (a, m b)) -> m (Maybe (m b))
lookup' x menv = do
  env <- menv
  case env of
    L.Nil           -> return Nothing
    L.Cons mkv rest -> do
      (k, v) <- mkv
      if k == x
        then return (Just v)
        else lookup' x rest

toList :: Monad m => m (Env m a b) -> m (L.List m (a, m b))
toList menv = do
  env <- menv
  case env of
    Nil -> return L.Nil
    Cons _ k v rest -> return $ L.Cons (return (k, v)) (toList rest)

fromList :: (Monad m, Ord a) => m (L.List m (a, m b)) -> m (Env m a b)
fromList l = insertAll' l nil

foldrE :: Monad m => (a -> m b -> m c -> m c) -> m c -> m (Env m a b) -> m c
foldrE f e ml = do
  l <- ml
  case l of
    Nil           -> e
    Cons _ k v xs -> f k v (foldrE f e xs)

select :: MonadPlus m => m (Env m a b) -> m (a, m b)
select env = foldrE (\a b c -> (return (a, b)) A.<|> c) mzero env

map :: Monad m => (a -> m b -> m b) -> m (Env m a b) -> m (Env m a b)
map f menv = do
  env <- menv
  case env of
    Nil -> nil
    Cons _ k v rest -> cons k (f k v) (map f rest)

all :: Monad m => (a -> m b -> m Bool) -> m (Env m a b) -> m Bool
all f menv = do
  env <- menv
  case env of
    Nil -> return True
    Cons _ k v rest -> do
      bool <- f k v
      if bool
        then all f rest
        else return False

any :: Monad m => (a -> m b -> m Bool) -> m (Env m a b) -> m Bool
any f menv = do
  env <- menv
  case env of
    Nil -> return False
    Cons _ k v rest -> do
      bool <- f k v
      if bool
        then return True
        else any f rest
