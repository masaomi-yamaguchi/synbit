{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wunused-imports #-}

-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Synthesis.Trace where

import           Value
import           Control.Monad.Sharing
import           Data.Monadic.List
import           Synthesis.LazyValue
import           Synthesis.ResidualExp
import           Name
-- import           Synthesis.LazyEvalG ()
import           Control.Applicative
import           Control.Monad

data Trace = TrNil
           | TrBranch Trace Int Trace
           | TrCon Name Bool [Trace]
           | TRConstL
  deriving Show

data MTrace m =
    MTrNil
  | MTrBranch Bool (m (MTrace m)) (m Int) (m (MTrace m)) -- e0 の MTrace, どのbranchを選んだか, 選んだbranchでのTrace 
  | MTrCon Bool (m Name) (m Bool) (m (List m (MTrace m))) -- コンストラクタでTraceは分岐する
  | MTrConstL

-- updated Trace
-- data UTrace m =
--     UTrNil
--   | UTrBranch (m (UTrace m)) (m Int) (m Int) (m (UTrace m)) -- e0 の UTrace, そもそものbranch, スイッチ先のBranch, そのbranchでのTrace(swなしなら2つのIntの値は同じ)
--   | UTrCon (m Name) (m Bool) (m (List m (UTrace m)))
--   | UTrConstL
instance Monad m => Convertible m (MTrace m) Trace where
  convert MTrNil = return TrNil
  convert (MTrBranch _ tr0 i tr) = do
    tr0' <- convert =<< tr0
    i' <- i
    tr' <- convert =<< tr
    return (TrBranch tr0' i' tr')
  convert (MTrCon _ name b trs) = do
    name' <- name
    b' <- b
    trs' <- convert =<< trs
    return (TrCon name' b' trs')
  convert MTrConstL = return TRConstL

instance Monad m
  => Convertible m (m (MValue m), m (MTrace m)) (Value, Trace) where
  convert (mv, mtr) = do
    v' <- convert =<< mv
    tr' <- convert =<< mtr
    return (v', tr')

instance Monad m => Shareable m (m (MRExp m), m (MTrace m)) where
  shareArgs f (r, tr) = do
    r' <- f r
    tr' <- f tr
    return (r', tr')

instance Monad m => Shareable m (MTrace m) where
  shareArgs _ MTrNil = return MTrNil
  shareArgs f (MTrBranch b tr0 i tr) =
    if b
    then return (MTrBranch True tr0 i tr)
    else do
      i' <- f i
      tr0' <- f tr0
      tr' <- f tr
      return (MTrBranch True tr0' i' tr')
  shareArgs f (MTrCon bb name b l) =
    if bb
    then return (MTrCon True name b l)
    else do
      b' <- f b
      l' <- f l
      return (MTrCon True name b' l')
  shareArgs _ MTrConstL = return MTrConstL

trNil :: Monad m => m (MTrace m)
trNil = return MTrNil

trBranch
  :: Monad m => (m (MTrace m)) -> (m Int) -> (m (MTrace m)) -> m (MTrace m)
trBranch e0_tr i tr = return $ MTrBranch False e0_tr i tr

trCon
  :: Monad m => (m Name) -> (m Bool) -> (m (List m (MTrace m))) -> m (MTrace m)
trCon name b l = return $ MTrCon False name b l
