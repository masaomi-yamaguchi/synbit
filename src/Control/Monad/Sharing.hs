{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Control.Monad.Sharing
    ( Sharing(..)
    , Delay(..)
    , Shareable(..)
    , SharingD
    , collect
    , collectFail
    , Convertible
    , convert
    , resultListIO
    , resultList) where

{-
A minimal implementation of http://hackage.haskell.org/package/explicit-sharing.
-}
import           Control.Applicative (Alternative(..))
import           Control.Delay
import           Control.Gen
import           Control.Monad (MonadPlus(..))
import qualified Data.IntMap.Strict as I
import           Unsafe.Coerce
import           Control.Monad.SearchTree
import           Debug.Trace
import           Control.Monad.Fail (MonadFail, fail)

import qualified Data.Bits as B

class MonadPlus s => Sharing s where
  share :: Shareable s a => s a -> s (s a)

type SharingD s = (Sharing s, Delay s)

class Shareable m a where
  shareArgs
    :: Monad n => (forall b. Shareable m b => m b -> n (m b)) -> a -> n a
  shareArgs _ a = return a

instance Monad m => Shareable m Int

instance Monad m => Shareable m Float

instance Monad m => Shareable m Bool

data Untyped = forall a. Untyped a

coer :: Untyped -> a
coer (Untyped a) = unsafeCoerce a

-- Specialized version 
data IUTrie = Bin {-# UNPACK #-} !Int {-# UNPACK #-} !Int !IUTrie !IUTrie
            | forall a. Tip {-# UNPACK #-} !Int a 
            | Empty 

emptyUn :: IUTrie
emptyUn = Empty
{-# INLINE emptyUn #-}

-- For debugging
showIUTrie :: IUTrie -> String
showIUTrie t = go 0 t ""
  where   
    parensIf b d r  = if b then "(" ++ d (")" ++ r) else d r 
    
    go _ Empty     = ("Empty" ++)
    go i (Tip k _) = parensIf (i > 0) $ ("Tip " ++) . shows k . (" _" ++ )
    go i (Bin p m t1 t2) = parensIf (i > 0) $
      ("Bin "++) . shows p . (" " ++ ) . shows m . (" " ++) . go 1 t1 . (" " ++ ) . go 1 t2 

nomatchPrefix :: Int -> Int -> Int -> Bool
nomatchPrefix k p m = mask k m /= p
{-# INLINE nomatchPrefix #-} 

checkZero :: Int -> Int -> Bool
checkZero k m = k B..&. m == 0 
{-# INLINE checkZero #-} 

mask :: Int -> Int -> Int 
mask k m = -- k B..&. (m - 1) 
           (k B..|. (m - 1)) B..&. B.complement m
{-# INLINE mask #-} 

joinT :: Int -> IUTrie -> Int -> IUTrie -> IUTrie
joinT p1 t1 p2 t2 
  | checkZero p1 m = Bin (mask p1 m) m t1 t2
  | otherwise      = Bin (mask p1 m) m t2 t1 
  where
    m = highestBit (B.xor p1 p2) 
    -- lowestBit x = x B..&. (-x)
    highestBit x = B.unsafeShiftL 1 (B.finiteBitSize x - 1 - B.countLeadingZeros x)
{-# INLINE joinT #-}
    

lookupUn :: Int -> IUTrie -> Maybe Untyped
lookupUn k t = lookupUnK k t Nothing Just
{-# INLINE lookupUn #-} 

lookupUnK :: Int -> IUTrie -> r -> (Untyped -> r) -> r
lookupUnK k t nothing just = seq k (go t)
  where
    go (Bin p m t1 t2)
      | nomatchPrefix k p m = nothing
      | checkZero k m = go t1
      | otherwise     = go t2
    go (Tip i x)
      | k == i    = just (Untyped x) 
      | otherwise = nothing
    go Empty = nothing 
{-# INLINE lookupUnK #-} 


insertUn :: Int -> Untyped -> IUTrie -> IUTrie
insertUn k (Untyped a) Empty     = Tip k a
insertUn k (Untyped a) t@(Tip kk aa)
  | k == kk   = Tip k a
  | otherwise = joinT k (Tip k a) kk t 
insertUn k a@(Untyped a') t@(Bin p m t1 t2)
  | nomatchPrefix k p m = joinT k (Tip k a') p t
  | checkZero k m       = Bin p m (insertUn k a t1) t2
  | otherwise           = Bin p m t1 (insertUn k a t2)

data Store =
  Store { index :: {-# UNPACK #-} !Int, table :: !IUTrie  }

newtype Lazy r a = Lazy { runLazy :: Store -> (Store -> a -> r) -> r }
  deriving Functor

instance Monoid n => Applicative (Lazy n) where
  pure = \a -> Lazy $ \s k -> k s a
  {-# INLINE pure #-}

  Lazy f <*> Lazy a = Lazy
    $ \s k -> f s $ \s' h -> a s' $ \s'' v -> k s'' (h v)
  {-# INLINE (<*>) #-}

instance Monoid n => Monad (Lazy n) where
  return = pure
  {-# INLINE return #-}

  Lazy m >>= f = Lazy $ \s k -> m s $ \s' a -> runLazy (f a) s' k
  {-# INLINE (>>=) #-}

instance Monoid n => Alternative (Lazy n) where
  empty = Lazy $ \s k -> mempty
  {-# INLINE empty #-}

  Lazy a <|> Lazy b = Lazy $ \s k -> a s k <> b s k
  {-# INLINE (<|>) #-}

instance Monoid n => MonadPlus (Lazy n) where


instance Monoid n => Sharing (Lazy n) where
  share a = memo (a >>= shareArgs share)

instance Gen n => Delay (Lazy n) where
  -- cost must be outside
  delay weight m = Lazy $ \s k -> cost weight (runLazy m s k)
  {-# INLINE delay #-} 

memo :: Lazy n a -> Lazy n (Lazy n a)
memo m = Lazy
  $ \s k
  -> let idx = index s
     in k s { index = idx + 1 }
        $ Lazy
        $ \s' k' ->
            lookupUnK idx (table s')
            (runLazy m s' $ \s'' v -> k' (s'' { table = insertUn idx (Untyped v) (table s'') }) v)
            (\v -> k' s' (coer v))
            
  
          --   case lookupUn idx (table s') of
          -- Just v  -> k' s' (coer v)
          -- Nothing -> runLazy m s'
          --   $ \s'' v
          --   -> k' (s'' { table = insertUn idx (Untyped v) (table s'') }) v

{-# INLINABLE memo #-}
collect :: Gen a => (forall s. (Sharing s, Delay s) => s a) -> a
collect m = runLazy m (Store 0 emptyUn) $ \_ a -> a

{-# INLINABLE collect #-}
collectFail
  :: Gen a => (forall s. (Sharing s, Delay s, MonadFail s) => s a) -> a
collectFail m = runLazy m (Store 0 emptyUn) $ \_ a -> a

{-# INLINABLE collectFail #-}
resultListIO :: (forall s. (Sharing s, Delay s, MonadFail s) => s a) -> IO [a]
resultListIO m = return $ dijkstra $ collectFail $ fmap pure m

resultList :: (forall s. (Sharing s, Delay s, MonadFail s) => s a) -> [a]
resultList m = dijkstra $ collectFail $ fmap pure m

instance Monoid n => MonadFail (Lazy n) where
  fail _ = mzero

-- |
-- Interface for convertible datatypes. The provided function
-- 'convArgs' is supposed to map the given function on every argument
-- of the given value and combine the results to give the converted
-- value.
--
-- We provide instances of the 'Convertible' class for some predefined
-- Haskell types. For flat types the function 'convArgs' just returns
-- its argument which has no arguments to which the given function
-- could be applied.
class Convertible m a b where
  convert :: a -> m b

instance Monad m => Convertible m Bool Bool where
  convert = return

instance Monad m => Convertible m Int Int where
  convert = return

instance Monad m => Convertible m Integer Integer where
  convert = return

instance Monad m => Convertible m Float Float where
  convert = return

instance Monad m => Convertible m Double Double where
  convert = return

instance Monad m => Convertible m Char Char where
  convert = return

instance Monad m => Convertible m [Bool] [Bool] where
  convert = return

instance Monad m => Convertible m [Int] [Int] where
  convert = return

instance Monad m => Convertible m [Integer] [Integer] where
  convert = return

instance Monad m => Convertible m [Float] [Float] where
  convert = return

instance Monad m => Convertible m [Double] [Double] where
  convert = return

instance Monad m => Convertible m [Char] [Char] where
  convert = return

-- |
-- An instance to convert ordinary lists into lists with monadic
-- elements.
instance (Monad m, Convertible m a b) => Convertible m [a] [m b] where
  convert = return . map convert

-- |
-- An instance to convert lists with monadic elements into ordinary
-- lists.
instance (Monad m, Convertible m a b) => Convertible m [m a] [b] where
  convert = mapM (>>= convert)

instance Monad m => Shareable m Integer where
  shareArgs _ = return

instance Monad m => Shareable m Double where
  shareArgs _ = return

instance Monad m => Shareable m Char where
  shareArgs _ = return

instance Monad m => Shareable m [Bool] where
  shareArgs _ = return

instance Monad m => Shareable m [Int] where
  shareArgs _ = return

instance Monad m => Shareable m [Integer] where
  shareArgs _ = return

instance Monad m => Shareable m [Float] where
  shareArgs _ = return

instance Monad m => Shareable m [Double] where
  shareArgs _ = return

instance Monad m => Shareable m [Char] where
  shareArgs _ = return

instance Monad m => Shareable m (a -> b) where
  shareArgs _ = return
