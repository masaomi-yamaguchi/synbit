{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns  #-}

module Control.Monad.SearchTree where

import           Control.Applicative  (Alternative (..))
import           Control.Delay
import           Control.Gen
import           Control.Monad        (MonadPlus (..), ap)
import           Data.Monoid          (Monoid (..))


import           Control.Arrow        (first, second)
import qualified Data.PQueue.Prio.Min as Q

import           Debug.Trace

newtype Search a = Search { runSearch :: Int -> SearchTree a }
  deriving Functor

instance Show a => Show (Search a) where
  show (Search s) = show (s 0)

instance Applicative Search where
  pure a = Search $ \r -> if r > 0 then Cost r (One a) else One a
  (<*>) = ap

instance Monad Search where
  return = pure
  Search s1 >>= f = Search $ \r -> aux (s1 r)
    where
      aux None         = None
      aux (Cost n t)   = Cost n (aux t)
      aux (One a)      = runSearch (f a) 0
      aux (Fork t1 t2) = Fork (aux t1) (aux t2)

instance Alternative Search where
  empty = Search $ \_ -> None
  f <|> g = Search $ \r -> if r > 0 then Cost r (Fork (runSearch f 0) (runSearch g 0)) else Fork (runSearch f r) (runSearch g r)

instance MonadPlus Search

instance Delay Search where
  delay n (Search s) = Search $ \r -> s (n + r)

instance Foldable Search where
  foldr c n = foldr c n . ($ 0) . runSearch

instance Semigroup (Search a) where
  (<>) = (<|>)

instance Monoid (Search a) where
  mempty = empty

instance Gen (Search a) where
  cost = delay

data SearchTree a =
  None | One a | Cost !Int (SearchTree a) | Fork (SearchTree a) (SearchTree a)
  deriving (Functor, Show)

instance Applicative SearchTree where
  pure = One
  (<*>) = ap

instance Alternative SearchTree where
  empty = None
  (<|>) = Fork

instance Monad SearchTree where
  return = pure
  None  >>= f = None
  One a >>= f = f a
  Cost n m >>= f = Cost n (m >>= f)
  Fork m1 m2 >>= f = Fork (m1 >>= f) (m2 >>= f)

instance MonadPlus SearchTree

instance Semigroup (SearchTree a) where
  (<>) = (<|>)

instance Monoid (SearchTree a) where
  mempty = empty

instance Gen (SearchTree a) where
  cost n m | n > 0     = Cost n m
           | otherwise = m

instance Delay SearchTree where
  delay n m | n > 0     = Cost n m
            | otherwise = m

instance Foldable SearchTree where
  foldr f c = foldr f c . dijkstra

printLevelWiseS :: Show a => Search a -> IO ()
printLevelWiseS (Search t) = printLevelWise (t 0)

printLevelWise :: Show a => SearchTree a -> IO ()
printLevelWise t = trav 0 False (SCons t SNil) SNil
  where
    trav _   _ SNil SNil = putStrLn "End"
    trav gen _ SNil qs   = do
      let gen' = gen + 1
      let str = "\n-- Generation: " ++ show gen' ++ " "
      putStrLn $ str ++ take (80 - length str) (repeat '-')
      trav (gen + 1) False (sreverse qs) SNil
    trav gen b (SCons q qs) re =
      case q of
        None      -> trav gen b qs re
        One a     -> do
          if b then putStr "," else return ()
          putStr (show a)
          trav gen True qs re
        Cost n q' ->
          if n - 1 > 0 then trav gen b qs (SCons (Cost (n-1) q') re)
          else              trav gen b qs (SCons q' re)
        Fork t1 t2 -> trav gen b qs (SCons t2 $ SCons t1 re)


dijkstra :: SearchTree a -> [a]
dijkstra t = trav (Q.singleton 0 t)
  where
    trav (Q.minViewWithKey -> Nothing) = []
    trav (Q.minViewWithKey -> Just ((n, t), q)) =
      case t of
        None       -> trav q
        One a      -> a : trav q
        Cost m t1  -> trav (Q.insert (n + m) t1 q)
        Fork t1 t2 -> trav (Q.insert (n + 1) t1 $ Q.insert (n + 1) t2 q)

data SList a = SNil | SCons a !(SList a)

lqueuep :: SearchTree a -> [a]
lqueuep t =
  let ~(qs, rs) = first (t:) $ go 1 qs
  in rs
  where
    go :: Int -> [SearchTree a] -> ([SearchTree a], [a])
    go 0 qs = ([], [])
    go len (q : qs) = case q of
      None  -> go (len - 1) qs
      One a -> second (a :) $ go (len - 1) qs
      Cost n t -> if n - 1 > 0 then first (Cost (n-1) t :) $ go len qs
                  else              first (           t :) $ go len qs
      Fork t1 t2 -> first (\x -> t1 : t2 : x) $ go (len + 1) qs

lqueue :: SearchTree a -> [a]
lqueue t =
  let qs = t : go 1 qs
  in extOne qs
  where
    extOne []           = []
    extOne (One a : qs) = a : extOne qs
    extOne (_     : qs) = extOne qs

    go :: Int -> [SearchTree a] -> [SearchTree a]
    go 0 qs = []
    go len (q : qs) = case q of
      None       -> go (len-1) qs
      One a      -> go (len-1) qs
      Cost n t   -> if n - 1 > 0 then Cost (n-1) t : go len qs
                    else              t : go len qs
      Fork t1 t2 -> t1 : t2 : go (len+1) qs


fqueue :: SearchTree a -> [a]
fqueue t = trav (SCons t SNil) SNil
  where
    trav SNil SNil = []
    trav SNil qs = trav (sreverse qs) SNil
    trav (SCons q qs) re =
      case q of
        None      -> trav qs re
        One a     -> a:trav qs re
        Cost n q' ->
          if n - 1 > 0 then trav qs (SCons (Cost (n-1) q') re)
          else              trav qs (SCons q' re)
        Fork t1 t2 -> trav qs (SCons t2 $ SCons t1 re)


sreverse :: SList a -> SList a
sreverse xs = rev xs SNil
  where
    rev SNil ys         = ys
    rev (SCons a xs) ys = rev xs (SCons a ys)



