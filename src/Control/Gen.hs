module Control.Gen where

class Monoid n => Gen n where
  cost :: Int -> n -> n

