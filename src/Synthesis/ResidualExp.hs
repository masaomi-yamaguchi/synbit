{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -Wunused-imports #-}

module Synthesis.ResidualExp where

import           Name
import           Control.Monad.IO.Class
import           Control.Monad.Sharing
import           Data.Monadic.List
import           Data.Monadic.Util
import           Synthesis.LazyExp
import qualified Synthesis.PureExpression as P
import           Data.Monadic.MBool
import           Control.Monad.Fail
import           Control.Monad
import           Synthesis.LazyEnv as LE

-- Monadic Residual Expression
data MRExp m =
    MRVar Bool (m Name)
  | MRCon Bool (m Bool) (m Name) (m (List m (MRExp m)))
  | MRNum Bool (m Integer)
  | MRChar Bool (m Char)
  | MRFun Bool (m Name) (m (MExp m)) (m (MREnv m))
  | MRRFun Bool (m Name) (m Name) (m (MExp m)) (m (MREnv m))
  | MRMRFun Bool
            (m Int)
            (m (List m (m Name, m Name, m (MExp m))))
            (m (MREnv m))
  | MRConstL Bool (m (MRExp m))
  | MRCaseB Bool (m (MRExp m)) (m (List m (MRBAlt m))) (m (MREnv m)) -- 評価を遅延させるのでEnvが必要

type MREnv m = LE.Env m Name (MRExp m)

type MRAlt m = (MPat, m (MGuard m), m (MExp m))

type MRBAlt m = (MRPat, m (MGuard m), m (MRBranch m))

data MRBranch m = MRBranch { mrBody :: m (MExp m)
                           , mrExitCond :: m (MRExp m)
                           , mrReconciler :: m (MRExp m)
                           }

type MRPat = P.Pat

instance Monad m => Shareable m (MRExp m) where
  shareArgs f (MRVar b name) =
    if b
    then return (MRVar True name)
    else do
      name' <- f name
      return (MRVar True name')
  shareArgs f (MRCon bb b n vs) =
    if bb
    then return (MRCon True b n vs)
    else do
      b' <- f b
      n' <- f n
      vs' <- f vs
      return (MRCon True b' n' vs')
  shareArgs f (MRNum b i) =
    if b
    then return (MRNum True i)
    else do
      i' <- f i
      return (MRNum True i')
  shareArgs f (MRChar b c) =
    if b
    then return (MRChar True c)
    else do
      c' <- f c
      return (MRChar True c')
  shareArgs f (MRFun b g e env) =
    if b
    then return (MRFun True g e env)
    else do
      g' <- f g
      e' <- f e
      env' <- f env
      return (MRFun True g' e' env')
  shareArgs f (MRRFun b g x e env) =
    if b
    then return (MRRFun True g x e env)
    else do
      g' <- f g
      x' <- f x
      e' <- f e
      env' <- f env
      return (MRRFun True g' x' e' env')
  shareArgs f (MRMRFun b i l env) =
    if b
    then return (MRMRFun b i l env)
    else do
      i' <- f i
      l' <- f l
      env' <- f env
      return (MRMRFun True i' l' env')
  shareArgs f (MRConstL b e) =
    if b
    then return (MRConstL b e)
    else do
      e' <- f e
      return (MRConstL True e')
  -- shareArgs f (MRCase e alt) = do
  --   e' <- f e
  --   alt' <- f alt
  --   return (MRCase e' alt')
  shareArgs f (MRCaseB b e balt env) =
    if b
    then return (MRCaseB b e balt env)
    else do
      e' <- f e
      balt' <- f balt
      env' <- f env
      return (MRCaseB True e' balt' env')

instance Monad m => Shareable m (MRPat, m (MGuard m), m (MRBranch m)) where
  shareArgs f (pat, g, b) = do
    g' <- f g
    b' <- f b
    return (pat, g', b')

instance Monad m => Shareable m (MRBranch m) where
  shareArgs f branch = do
    body' <- f (mrBody branch)
    exitCond' <- f (mrExitCond branch)
    reconciler' <- f (mrReconciler branch)
    return
      $ MRBranch { mrBody = body'
                 , mrExitCond = exitCond'
                 , mrReconciler = reconciler'
                 }

-- MREXpでTrue, Falseを表す項をHaskellのTrue, Falseに変換
-- それ以外はmzeroへ
-- guardに使う
convertRB :: MonadPlus m => m (MRExp m) -> m Bool
convertRB me = do
  e <- me
  case e of
    (MRCon _ mb mname mlist) -> ifM
      mb
      mzero
      (do
         name <- mname
         case name of
           NTrue  -> true
           NFalse -> false)

getFreshMRVar :: MonadIO m => UniqSupply -> m (MRExp m)
getFreshMRVar a = do
  x <- liftIO $ getFresh a
  return (MRVar False (return (SName x)))

-- Value になってる時しか使ってはいけない
eqRExp :: (MonadFail m, MonadPlus m) => MRExp m -> MRExp m -> m Bool
eqRExp (MRNum _ mi1) (MRNum _ mi2) = do
  i1 <- mi1
  i2 <- mi2
  if i1 == i2
    then true
    else false
eqRExp (MRChar _ mc1) (MRChar _ mc2) = do
  c1 <- mc1
  c2 <- mc2
  if c1 == c2
    then true
    else false
eqRExp (MRCon _ b1 mname1 vs1) (MRCon _ b2 mname2 vs2) = do
  False <- b1
  False <- b2
  name1 <- mname1
  name2 <- mname2
  if name1 == name2
    then liftM2' go vs1 vs2
    else false
  where
    go Nil Nil = true
    go (Cons mv1 rest1) (Cons mv2 rest2) = do
      v1 <- mv1
      v2 <- mv2
      b <- eqRExp v1 v2
      -- if b then go =< rest1 =<< rest2 else false
      if b
        then liftM2' go rest1 rest2
        else false
