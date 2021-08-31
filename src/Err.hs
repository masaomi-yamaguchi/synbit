{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Err where

import Control.Monad.Except
import RunTimeException

data Err a = Bad String | Ok a

instance Show a => Show (Err a) where
  show (Ok a) = "Ok " ++ show a
  show (Bad s) = "!Error: " ++ s

instance Functor Err where
  fmap f (Ok a)  = Ok (f a)
  fmap f (Bad s) = Bad s

instance Applicative Err where
  pure = return
  Ok f  <*> Ok a  = Ok (f a)
  Ok f  <*> Bad s = Bad s
  Bad s <*> _     = Bad s

instance Monad Err where
  return = Ok
  Ok a >>= f  = f a
  Bad s >>= f = Bad s

instance MonadError [Char] Err where
  throwError = Bad
  catchError (Ok a)  f = Ok a
  catchError (Bad s) f = f s
