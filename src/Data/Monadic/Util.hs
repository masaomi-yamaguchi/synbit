{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.Monadic.Util where

import           Name
import           Loc
import           Control.Monad.Sharing
import           Data.IORef
import           Syntax.Type

instance Monad m => Shareable m Name where
  shareArgs _ = return

-- いらないかも
instance Monad m => Shareable m Loc where
  shareArgs _ = return

eqM :: (Monad m, Eq a) => m a -> m a -> m Bool
eqM mn mn' = do
  n <- mn
  n' <- mn'
  return (n == n')

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mbool a b = do
  bool <- mbool
  if bool
    then a
    else b

(<@>) :: Monad m => m (m a -> m b) -> m a -> m b
mf <@> ma = do
  f <- mf
  f ma

instance (Monad m, Shareable m b) => Shareable m (Name, m b) where
  shareArgs f (a, b) = do
    b' <- f b
    return (a, b')

instance (Monad m, Shareable m b) => Shareable m (TyVar, m b) where
  shareArgs f (a, b) = do
    b' <- f b
    return (a, b')

instance (Monad m, Shareable m b) => Shareable m (Int, m b) where
  shareArgs f (a, b) = do
    b' <- f b
    return (a, b')

instance (Monad m, Shareable m a, Shareable m b, Shareable m c)
  => Shareable m (m a, m b, m c) where
  shareArgs f (a, b, c) = do
    a' <- f a
    b' <- f b
    c' <- f c
    return (a', b', c')

instance (Monad m, Shareable m b) => Shareable m (Maybe (m b)) where
  shareArgs _ Nothing = return Nothing
  shareArgs f (Just b) = do
    b' <- f b
    return (Just b')

pair :: Monad m => m a -> m b -> m (m a, m b)
pair a b = return (a, b)

type UniqSupply = IORef Int

getFresh :: UniqSupply -> IO Int
getFresh a = do
  x <- readIORef a
  modifyIORef a (+ 1)
  return x

liftM2' :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
liftM2' f ma mb = do
  a <- ma
  b <- mb
  f a b

(=<) :: Monad m => (a -> b -> m c) -> m a -> b -> m c
(=<) f ma b = do
  a <- ma
  f a b

