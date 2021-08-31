module Control.Delay where

class Delay f where
  delay :: Int -> f a -> f a
