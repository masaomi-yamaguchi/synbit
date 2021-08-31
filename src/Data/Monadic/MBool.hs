module Data.Monadic.MBool where

import           Data.Monadic.List

(!||) :: Monad m => m Bool -> m Bool -> m Bool
mb1 !|| mb2 = do
  b1 <- mb1
  b2 <- mb2
  return (b1 || b2)

(!&&) :: Monad m => m Bool -> m Bool -> m Bool
mb1 !&& mb2 = do
  b1 <- mb1
  b2 <- mb2
  return (b1 && b2)

andM :: Monad m => m (List m Bool) -> m Bool
andM = foldrML (!&&) true

orM :: Monad m => m (List m Bool) -> m Bool
orM = foldrML (!||) false

false :: Monad m => m Bool
false = return False

true :: Monad m => m Bool
true = return True
