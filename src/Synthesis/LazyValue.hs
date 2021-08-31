{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wunused-imports #-}

module Synthesis.LazyValue where

import           Name
import           Control.Monad.Sharing
import           Data.Monadic.List
import           Data.Monadic.Util
import           Data.Monadic.MBool
import           Control.Monad
import           Loc
import           Value

-- import           Synthesis.LazyExp
data MValue m = MVCon Bool (m Name) (m (List m (MValue m)))
              | MVNum Bool (m Integer)
              | MVChar Bool (m Char)

type MVEnv m = List m (m Name, m (MValue m))

-- partial lens
newtype MLens m a b = MLens { runMLens :: m (m a -> m (m b, m (m b -> m a))) }

newtype MStore m = MStore (m (List m (m Loc, m (MValue m))))

instance Monad m => Shareable m (MValue m) where
  shareArgs f (MVCon b name vs) =
    if b
    then return (MVCon True name vs)
    else do
      name' <- f name
      vs' <- f vs
      return (MVCon True name' vs')
  shareArgs f (MVNum b i) =
    if b
    then return (MVNum True i)
    else do
      i' <- f i
      return (MVNum True i')
  shareArgs f (MVChar b c) =
    if b
    then return (MVChar True c)
    else do
      c' <- f c
      return (MVChar True c')

  -- shareArgs f (MVFun g e env) = do
  --   g' <- f g
  --   e' <- f e
  --   env' <- f env
  --   return (MVFun g' e' env')
  -- shareArgs f (MVRFun g x e env) = do
  --   g' <- f g
  --   x' <- f x
  --   e' <- f e
  --   env' <- f env
  --   return (MVRFun g' x' e' env')
  -- shareArgs f (MVMFun i l env) = do
  --   i' <- f i
  --   l' <- f l
  --   env' <- f env
  --   return (MVMFun i' l' env')
instance Monad m => Shareable m (MLens m (MStore m) (MValue m)) where
  shareArgs f (MLens l) = do
    l' <- f l
    return (MLens l')

equalM :: MonadPlus m => m (MValue m) -> m (MValue m) -> m Bool
equalM mv1 mv2 = do
  v1 <- mv1
  v2 <- mv2
  case (v1, v2) of
    (MVCon _ mn vs, MVCon _ mn' vs') -> (mn `eqM` mn')
      !&& andM (zipWithML equalM vs vs')
    (MVChar _ c, MVChar _ c') -> c `eqM` c'
    (MVNum _ i, MVNum _ i') -> i `eqM` i'
    (_, _) -> mzero

equalVM :: Monad m => Value -> m (MValue m) -> m Bool
equalVM v1 mv2 = do
  v2 <- mv2
  case (v1, v2) of
    (VCon n vs, MVCon _ mn' vs') -> do
      n' <- mn'
      if n == n'
        then and2ML vs vs'
        else return False
    (VChar c, MVChar _ mc') -> do
      c' <- mc'
      return (c == c')
    (VNum i, MVNum _ mi') -> do
      i' <- mi'
      return (i == i')
    (_, _) -> return False
  where
    and2ML :: Monad m => [Value] -> m (List m (MValue m)) -> m Bool
    and2ML l1 ml2 = do
      l2 <- ml2
      case (l1, l2) of
        ([], Nil) -> return True
        (x:xs, Cons y ys) -> do
          b <- equalVM x y
          if b
            then and2ML xs ys
            else return False
        _ -> return False

lessM :: MonadPlus m => m (MValue m) -> m (MValue m) -> m Bool
lessM mv1 mv2 = do
  v1 <- mv1
  v2 <- mv2
  case (v1, v2) of
    (MVNum _ i, MVNum _ i') -> i `lessM` i'
    (_, _) -> mzero
  where
    lessM mn mn' = do
      n <- mn
      n' <- mn
      return (n < n')

mVTrue :: Monad m => m (MValue m)
mVTrue = return $ MVCon False (return NTrue) nil

mVFalse :: Monad m => m (MValue m)
mVFalse = return $ MVCon False (return NFalse) nil

-- MREXpでTrue, Falseを表す項をHaskellのTrue, Falseに変換
-- それ以外はmzeroへ
-- guardに使う
convertVB :: MonadPlus m => m (MValue m) -> m Bool
convertVB me = do
  e <- me
  case e of
    (MVCon _ mname mlist)
      -> (do
            name <- mname
            case name of
              NTrue  -> true
              NFalse -> false
              _      -> mzero)
    _ -> mzero

instance Monad m => Convertible m (MValue m) Value where
  convert (MVCon _ mname ml) = do
    name <- mname
    l <- ml
    l' <- convert l
    return (VCon name l')
  convert (MVNum _ mi) = VNum <$> mi
  convert (MVChar _ mc) = VChar <$> mc
  -- -- import           Synthesis.LazyExp
  -- data MValue m = MVCon (m Name) (m (List m (MValue m)))
  --               | MVNum (m Integer)
  --               | MVChar (m Char)
