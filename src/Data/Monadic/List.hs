{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

-- |
-- Module      : Data.Monadic.List
-- Copyright   : Chung-chieh Shan, Oleg Kiselyov, and Sebastian Fischer
-- License     : PublicDomain
-- Maintainer  : Sebastian Fischer (sebf\@informatik.uni-kiel.de)
-- Stability   : experimental
--
-- This library provides lists with monadic head and tail as an
-- example for nested monadic data that can be used with the
-- combinator @share@ for explicit sharing.
module Data.Monadic.List where

import           Control.Monad
import           Control.Monad.Sharing (Shareable(..), Convertible(..))
import           Control.Monad.Fail

-- | Data type for lists where both the head and tail are monadic.
data List m a = Nil
              | Cons (m a) (m (List m a))

-- | The empty monadic list.
nil :: Monad m => m (List m a)
nil = return Nil

-- | Constructs a non-empty monadic list.
cons :: Monad m => m a -> m (List m a) -> m (List m a)
cons x xs = return (Cons x xs)

-- | Checks if monadic list is empty.
isEmpty :: Monad m => m (List m a) -> m Bool
isEmpty ml = do
  l <- ml
  case l of
    Nil      -> return True
    Cons _ _ -> return False

-- |
-- Yields the head of a monadic list. Relies on 'MonadPlus' instance
-- to provide a failing implementation of 'fail'.
first :: (MonadFail m, MonadPlus m) => m (List m a) -> m a
first ml = do
  Cons x _ <- ml
  x

-- |
-- Yields the tail of a monadic list. Relies on 'MonadPlus' instance
-- to provide a failing implementation of 'fail'.
rest :: (MonadFail m, MonadPlus m) => m (List m a) -> m (List m a)
rest ml = do
  Cons _ xs <- ml
  xs

-- |
-- This instance allows to use nested monadic lists as argument to the
-- 'Control.Monad.Sharing.share' combinator.
instance (Monad m, Shareable m a) => Shareable m (List m a) where
  shareArgs _ Nil = return Nil
  shareArgs f (Cons x xs) = do
    y <- f x
    ys <- f xs
    return (Cons y ys)

-- |
-- This instance enables the function 'Control.Monad.Sharing.convert'
-- to transform ordinary Haskell lists into nested monadic lists.
instance (Monad m, Convertible m a b) => Convertible m [a] (List m b) where
  convert [] = return Nil
  convert (x:xs) = return (Cons (convert x) (convert xs))

-- |
-- This instance enables the function 'Control.Monad.Sharing.convert'
-- to transform nested monadic lists into ordinary Haskell lists.
instance (Monad m, Convertible m a b) => Convertible m (List m a) [b] where
  convert Nil = return []
  convert (Cons x xs) = do
    y <- x >>= convert
    ys <- xs >>= convert
    return (y:ys)

-- map2のListとMList版
map2ML :: Monad m => (a -> m b -> m c) -> [a] -> m (List m b) -> m (List m c)
map2ML f l1 ml2 = do
  l2 <- ml2
  case (l1, l2) of
    ([], _) -> nil
    (_, Nil) -> nil
    (x:xs, Cons my mys) -> cons (f x my) (map2ML f xs mys)

-- 以下のmapやfoldは、fのshareをよく考えて実装しないとおかしくなるので、よーく考えて実装する事！！！
mapML :: Monad m => (m a -> m b) -> m (List m a) -> m (List m b)
mapML f = foldrML (\a ml' -> cons (f a) ml') nil

unzipML :: Monad m => m (List m (m a, m b)) -> m (m (List m a), m (List m b))
unzipML = foldrML
  (\p ret -> do
     (a, b) <- p
     (as, bs) <- ret
     return (cons a as, cons b bs))
  (return (nil, nil))

reverseML :: Monad m => m (List m a) -> m (List m a)
reverseML = revAppend nil
  where
    revAppend e ml = do
      l <- ml
      case l of
        Nil       -> e
        Cons x xs -> revAppend (cons x e) xs

foldrML :: Monad m => (m a -> m b -> m b) -> m b -> m (List m a) -> m b
foldrML f e ml = do
  l <- ml
  case l of
    Nil       -> e
    Cons x xs -> f x (foldrML f e xs)

lengthML :: Monad m => m (List m a) -> m Int
lengthML = foldrML
  (\_ mi -> do
     i <- mi
     return (i + 1))
  (return 0)

foldriML
  :: Monad m => (m a -> m Int -> m b -> m b) -> m b -> m (List m a) -> m b
foldriML f e ml = go f e ml (return 0)
  where
    go f e ml i = do
      l <- ml
      case l of
        Nil       -> e
        Cons x xs -> f x i (go f e xs (incM i))

    incM mi = do
      i <- mi
      return (i + 1)

foldrML2 :: MonadPlus m
         => (m a -> m b -> m c -> m c)
         -> m c
         -> m (List m a)
         -> m (List m b)
         -> m c
foldrML2 f e ml1 ml2 = do
  l1 <- ml1
  case l1 of
    Nil       -> e
    Cons x xs -> do
      l2 <- ml2
      case l2 of
        Nil       -> e
        Cons y ys -> f x y (foldrML2 f e xs ys)

zipWithML :: MonadPlus m
          => (m a -> m b -> m c)
          -> m (List m a)
          -> m (List m b)
          -> m (List m c)
zipWithML f ml1 ml2 = do
  l1 <- ml1
  case l1 of
    Nil       -> nil
    Cons x xs -> do
      l2 <- ml2
      case l2 of
        Nil       -> nil
        Cons y ys -> cons (f x y) $ zipWithML f xs ys

zipWithML_Fail :: MonadPlus m
               => (m a -> m b -> m c)
               -> m (List m a)
               -> m (List m b)
               -> m (List m c)
zipWithML_Fail f ml1 ml2 = do
  l1 <- ml1
  case l1 of
    Nil       -> do
      l2 <- ml2
      case l2 of
        Nil       -> nil
        Cons y ys -> mzero
    Cons x xs -> do
      l2 <- ml2
      case l2 of
        Nil       -> mzero
        Cons y ys -> cons (f x y) $ zipWithML_Fail f xs ys

nthML :: MonadPlus m => m (List m a) -> m Int -> m a
nthML ml mi = do
  i <- mi
  go i ml
  where
    go i ml = do
      l <- ml
      case l of
        Nil       -> mzero
        Cons x xs -> if i == 0
                     then x
                     else go (i - 1) xs

mapToML :: Monad m => (a -> m b) -> [a] -> m (List m b)
mapToML f = foldr (cons . f) nil
