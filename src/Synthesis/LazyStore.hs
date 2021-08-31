{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wunused-imports #-}

module Synthesis.LazyStore where

import           Prelude hiding (lookup)
import qualified Data.Monadic.List as L
import           Control.Monad
import           Data.Monadic.Util hiding (pair)
import           Control.Monad.Sharing

-- keyが小さい順にsortして保持
data Store m a b = Nil
                 | Cons Bool (m (a, m b)) (m (Store m a b))

instance (Monad m, Eq a, Shareable m (a, m b))
  => Shareable m (Store m a b) where
  shareArgs _ Nil = return Nil
  shareArgs f (Cons isShared x xs)
    | isShared = return $ Cons True x xs
  shareArgs f (Cons isShared x xs)
    | otherwise = do
      y <- f x
      ys <- f xs
      return $ Cons True y ys

nil :: Monad m => m (Store m a b)
nil = return Nil

cons :: Monad m => m (a, m b) -> m (Store m a b) -> m (Store m a b)
cons a l = return $ Cons False a l

empty :: Monad m => m (Store m a b)
empty = nil

-- share 不要
lookup :: (Monad m, Ord a) => a -> Store m a b -> m (Maybe (m b))
lookup x env = case env of
  Nil -> return Nothing
  Cons _ mkv rest -> do
    (k, v) <- mkv
    if k == x
      then return (Just v)
      else if k > x
           then return Nothing
           else lookup x =<< rest

-- share不要
-- s1 から優先して探し、見つからなければ s2 から探す
lookupUpd :: (Monad m, Ord a)
          => a
          -> m (Store m a b)
          -> m (Store m a b)
          -> m (Maybe (m b))
lookupUpd x s1 s2 = do
  look1 <- lookup x =<< s1
  case look1 of
    Just v  -> return $ Just v
    Nothing -> do
      look2 <- lookup x =<< s2
      case look2 of
        Just v  -> return $ Just v
        Nothing -> return Nothing

-- share 不要
insert :: (Monad m, Ord a) => a -> m b -> m (Store m a b) -> m (Store m a b)
insert x v menv = do
  env <- menv
  case env of
    Nil -> cons (return (x, v)) nil
    Cons _ mkv rest -> do
      (k, v') <- mkv
      if k == x
        then cons (return (x, v)) rest
        else if k > x
             then cons (return (x, v)) (cons (pair k v') rest)
             else cons (pair k v') (insert x v rest)

insertAll
  :: (Monad m, Ord a) => m (Store m a b) -> m (Store m a b) -> m (Store m a b)
insertAll mbind env = do
  bind <- mbind
  case bind of
    Nil -> env
    Cons _ mkv rest -> do
      (k, v) <- mkv
      insert k v (insertAll rest env)

-- どちらのstore もshareされていたほうがいい
-- Valueの比較を行うため
-- mergeも何回するかわからないし
merge :: (MonadPlus m, Ord a)
      => (b -> b -> m Bool)
      -> m (Store m a b)
      -> m (Store m a b)
      -> m (Store m a b)
merge eq ms1 ms2 = do
  s1 <- ms1
  s2 <- ms2
  go s1 s2
  where
    go Nil Nil = nil
    go (Cons b kv rest) Nil = return $ Cons b kv rest
    go Nil (Cons b kv rest) = return $ Cons b kv rest
    go (Cons b1 mkv1 rest1) (Cons b2 mkv2 rest2) = do
      (k1, mv1) <- mkv1
      (k2, mv2) <- mkv2
      if k1 == k2
        then do
          v1 <- mv1
          v2 <- mv2
          b <- eq v1 v2
          if b
            then cons (return (k1, return v1)) (go =< rest1 =<< rest2)
            else mzero
        else if k1 < k2
             then do
               rest1' <- rest1
               cons (pair k1 mv1) $ go rest1' (Cons b2 (pair k2 mv2) rest2)
             else cons (pair k2 mv2)
               $ go (Cons b1 (pair k1 mv1) rest1) =<< rest2

--  k < start,
--  start <= k < end
-- に分ける。 k >= end は捨てる
-- Value以外のshareは壊れる
split :: (MonadPlus m, Ord a)
      => a
      -> a
      -> m (Store m a b)
      -> m (m (Store m a b), m (Store m a b))
split start end ms = do
  s <- ms
  case s of
    Nil -> return (nil, nil)
    Cons b kv rest -> do
      (k, v) <- kv
      (s1, s2) <- split start end rest
      if k < start
        then pair (cons (pair k v) s1) s2
        else if k < end
             then pair s1 (cons (pair k v) s2)
             else return (empty, empty) -- 小さい順なので、k >= end になったらそれ以降は捨てる

pair a b = return (a, b)

map2ML_ f l1 ml2 = do
  l2 <- ml2
  case (l1, l2) of
    (_, L.Nil) -> nil
    (x:xs, L.Cons my mys) -> cons (f x my) (map2ML_ f xs mys)

