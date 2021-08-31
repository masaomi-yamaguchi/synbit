{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wunused-imports #-}

-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Synthesis.LazyEvalU where

import           Control.Monad.Sharing
import           Synthesis.LazyExp
import           Data.Monadic.List
import           Data.Monadic.Util
import           Data.Monadic.MBool
import           Synthesis.ResidualExp
import           Synthesis.LazyEnv as E
import           Name
import           Synthesis.PureExpression
import           Control.Monad.Fail
import           Control.Monad
import           Debug.Trace

-- env, e はshare済みのものを渡すこと！
evalU :: (MonadPlus m, Sharing m, MonadFail m)
      => m (MREnv m)
      -> MExp m
      -> m (MRExp m)
evalU env (MEVar _ mx) = do
  x <- mx
  look <- E.lookup x env
  case look of
    Just r  ->
      -- x >>= (\x -> liftIO $ putStrLn $ "x = " ++ show x)
      r
    Nothing -> return (MRVar False (return x))
evalU env (MEAbs _ x me) = return (MRFun False x me env)
evalU env (MEApp _ e1 e2) = do
  mr1 <- share $ evalU env =<< e1
  r1 <- mr1
  mr2 <- share $ evalU env =<< e2
  r2 <- mr2
  appR r1 r2
evalU env (MEAdd _ e1 e2) = do
  r1 <- evalU env =<< e1
  r2 <- evalU env =<< e2
  case (r1, r2) of
    (MRNum _ mi1, MRNum _ mi2) -> do
      i1 <- mi1
      i2 <- mi2
      return $ MRNum False $ return (i1 + i2)
evalU env (MEEq _ e1 e2) = do
  r1 <- evalU env =<< e1
  r2 <- evalU env =<< e2
  ans <- check
    r1
    r2 -- r1, r2はshareしなくてよい。checkの構造的に問題ない
  if ans
    then return $ MRCon False false (return NTrue) nil
    else return $ MRCon False false (return NFalse) nil
  where
    check :: (MonadFail m, MonadPlus m) => MRExp m -> MRExp m -> m Bool
    check r1 r2 = case (r1, r2) of
      (MRNum _ mi1, MRNum _ mi2) -> do
        i1 <- mi1
        i2 <- mi2
        if i1 == i2
          then true
          else false
      (MRChar _ mc1, MRChar _ mc2) -> do
        c1 <- mc1
        c2 <- mc2
        if c1 == c2
          then true
          else false
      (MRCon _ mb1 mname1 rs1, MRCon _ mb2 mname2 rs2) -> do
        False <- mb1
        False <- mb2
        name1 <- mname1
        name2 <- mname2
        if name1 == name2
          then checkL rs1 rs2
          else false
      _ -> mzero

    checkL :: (MonadFail m, MonadPlus m)
           => m (List m (MRExp m))
           -> m (List m (MRExp m))
           -> m Bool
    checkL ml1 ml2 = do
      l1 <- ml1
      l2 <- ml2
      case (l1, l2) of
        (Nil, Nil) -> true
        (Cons mx xs, Cons my ys) -> do
          x <- mx
          y <- my
          ifM (check x y) (checkL xs ys) false
        _ -> false
evalU env (MENeg _ e) = do
  MRNum _ mi <- evalU env =<< e
  i <- mi
  return $ MRNum False $ return (-i)
evalU _ (MENum _ k) = return $ MRNum False k
evalU _ (MEChar _ k) = return $ MRChar False k
evalU env (MECon _ mb n es) = do
  let rs = mapML (\e -> evalU env =<< e) es
  return $ MRCon False mb n rs
evalU env (MECase _ e0 alts) = do
  mr0 <- share $ evalU env =<< e0
  r0 <- mr0
  evalAltsU r0 alts env
  where
    evalAltsU :: (MonadPlus m, Sharing m, MonadFail m)
              => MRExp m
              -> m (List m (MAlt m))
              -> m (MREnv m)
              -> m (MRExp m)
    evalAltsU r0 malts env = do
      alts <- malts
      case alts of
        Nil -> mzero -- 全てのBranchにマッチしなかった時
        Cons mpge rest -> do
          (p, g, e) <- mpge
          res <- findMatch p r0 -- findMatchの結果はenv'でshareされるので、ここではshare不要
          case res of
            Nothing   -> evalAltsU r0 rest env
            Just bind -> do
              env' <- share $ E.insertAll bind env
              g' <- convertRB $ evalU env' =<< g
              if g'
                then evalU env' =<< e
                else evalAltsU r0 rest env
evalU env (MECaseB _ e0 balts) = do
  let r0' = evalU env =<< e0
  let balts' = evalBAltsU balts env
  return $ MRCaseB False r0' balts' env
  where
    evalBAltsU :: (MonadPlus m, Sharing m, MonadFail m)
               => m (List m (MBAlt m))
               -> m (MREnv m)
               -> m (List m (MRBAlt m))
    evalBAltsU mbalts env = mapML
      (\mpgb -> do
         (pat, guard, branch) <- mpgb
         MBranch { mBody = body, mExitCond = exit, mReconciler = reconciler }
           <- branch
         let exit' = evalU env =<< exit
         let reconciler' = evalU env =<< reconciler
         let branch' = return $ MRBranch body exit' reconciler'
         return (pat, guard, branch'))
      mbalts
evalU env (MEConstL _ e) = return $ MRConstL False (evalU env =<< e)
evalU env _ = do
  t <- mTrue
  evalU env t

appR
  :: (MonadPlus m, Sharing m, MonadFail m) => MRExp m -> MRExp m -> m (MRExp m)
appR r1 r2 = case r1 of
  MRFun _ mx e oenv -> do
    x <- mx
    env' <- share (E.insert x (return r2) oenv)
    evalU env' =<< e
  MRRFun _ mf mx e oenv -> do
    f <- mf
    x <- mx
    env' <- share $ E.insert x (return r2) $ E.insert f (return r1) oenv
    evalU env' =<< e
  MRMRFun _ i funs oenv -> do
    (_, mx, e) <- nthML funs i
    x <- mx
    env' <- share
      $ E.insert x (return r2)
      $ foldriML
        (\mfxe i env' -> do
           (mf, mx, e) <- mfxe
           f <- mf
           let r = return $ MRMRFun False i funs oenv
           E.insert f r env')
        oenv
        funs
    evalU env' =<< e
  MRVar _ x -> do
    x <- x
    trace ("debug: MRVar " ++ show x) undefined
  MRCon _ b name l -> do
    b <- b
    name <- name
    trace ("debug: MRCon " ++ show b ++ " " ++ show name) undefined

-- eはshareされていることを前提
findMatch
  :: (MonadPlus m, Sharing m) => MRPat -> MRExp m -> m (Maybe (m (MREnv m)))
findMatch pat e = case (pat, e) of
  (PNum i, MRNum _ mj) -> do
    j <- mj
    if i == j
      then return $ Just empty
      else return $ Nothing
  (PChar i, MRChar _ mj) -> do
    j <- mj
    if i == j
      then return $ Just empty
      else return Nothing
  (PVar x, _) -> return $ Just $ singleton x (return e)
  (PCon name1 ps, MRCon _ b mname2 mrs) -> do
    name2 <- mname2
    if name1 == name2
      then go ps mrs
      else return Nothing
    where
      go :: (MonadPlus m, Sharing m)
         => [Pat]
         -> m (List m (MRExp m))
         -> m (Maybe (m (MREnv m)))
      go ps mrs = do
        rs <- mrs
        case (ps, rs) of
          ([], Nil) -> return $ Just empty
          (p:rest_p, Cons mr rest_r) -> do
            r <- mr
            env1 <- findMatch p r
            env2 <- go rest_p rest_r
            return $ E.insertAll <$> env1 <*> env2
  (_, _) -> return Nothing
