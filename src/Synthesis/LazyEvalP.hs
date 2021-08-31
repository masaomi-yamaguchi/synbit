{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- {-# OPTIONS_GHC -Wunused-imports #-}
-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Synthesis.LazyEvalP where

import           Value hiding (Store)
import           Control.Monad.Sharing (resultListIO, Convertible(..)
                                      , Shareable(..), Sharing(..))
import           Synthesis.LazyExp
import           Control.Monad.IO.Class
import           Data.Monadic.List
import           Data.Monadic.Util
import           Data.Monadic.MBool
import           Control.Monad
import           Synthesis.LazyValue
import           Synthesis.ResidualExp
import qualified Synthesis.LazyEnv as E
import qualified Synthesis.LazyStore as S
import           Name
import           Synthesis.PureExpression
import qualified Syntax.Typed as TD
import           Syntax.Type (LExp)
import           Data.List (partition)
import qualified Eval as EV (evalAsUsual, defaultEnv, Env)
import           Err
import           Synthesis.LazyEvalU
import           Synthesis.LazyEvalG
import           Control.Monad.Fail (MonadFail)

type Store m = S.Store m Loc (MRExp m)

-- env, mv, meはshareされていることを仮定
evalP :: (MonadPlus m, Sharing m, MonadFail m)
      => m (MREnv m)
      -> Loc
      -> m (MRExp m)
      -> m (MRExp m)
      -> m (Store m)
evalP env start mv me = do
  v <- mv
  e <- me
  evalP_ env start v e

-- env, v, mexpはshareされていることを仮定
evalP_ :: (MonadPlus m, Sharing m, MonadFail m)
       => m (MREnv m)
       -> Loc
       -> MRExp m
       -> MRExp m
       -> m (Store m)
evalP_ env start v (MRVar _ mx) = do
  x <- mx
  case x of
    NameI i -> S.insert i (return v) S.empty
evalP_ env start (MRCon _ vb mvname vs) (MRCon _ eb mename es) = do
  False <- vb -- Value は bidirectional ではない
  True <- eb -- Residual Exp は bidirectional
  vname <- mvname
  ename <- mename
  if vname == ename
    then go vs es
    else do
      -- liftIO $ putStrLn "Err: Update on constant."
      mzero
  where
    go mvs mes = do
      vs <- mvs
      es <- mes
      case (vs, es) of
        (Nil, Nil) -> S.empty
        (Cons v rest1, Cons e rest2) -> do
          mu1 <- share (evalP env start v e)
          mu2 <- share (go rest1 rest2)
          S.merge eqRExp mu1 mu2
evalP_ env start v (MRConstL _ e) = do
  v' <- share $ evalG env start =<< e
  b <- eqRExp v =<< v'
  if b
    then S.empty
    else do
      -- liftIO $ putStrLn "put Err. MRConstL"
      mzero
evalP_ env start v (MRCaseB _ e0 balts oenv) = do
  mv0 <- share $ evalG env start =<< e0
  v0 <- mv0
  evalBAltsP env start v e0 v0 balts balts oenv
  where
    evalBAltsP :: (MonadPlus m, Sharing m, MonadFail m)
               => m (MREnv m)
               -> Loc
               -> MRExp m
               -> m (MRExp m)
               -> MRExp m
               -> m (List m (MRBAlt m))
               -> m (List m (MRBAlt m))
               -> m (MREnv m)
               -> m (Store m)
    evalBAltsP env start v e0 v0 obalts mbalts oenv = do
      Just (heads, p, g, mb, bind)
        <- findFirstMatchB env v0 nil mbalts oenv -- heads以外はshareされている。headsは後に1回しか使われないので無問題
      b <- mb
      exit <- mrExitCond b
      exit' <- convertRB $ appR exit v
      if exit'
        then do
          -- liftIO $ putStrLn "orginal branch was taken"
          putE0 env bind start v e0 oenv p g heads =<< mrBody b
        else do
          -- liftIO $ putStrLn "branch switch"
          doReconcile env start v e0 v0 obalts oenv

    findFirstMatchB
      :: (MonadPlus m, Sharing m, MonadFail m)
      => m (MREnv m)
      -> MRExp m
      -> m (List m (MRBAlt m))
      -> m (List m (MRBAlt m))
      -> m (MREnv m)
      -> m
        (Maybe
           ( m (List m (MRBAlt m))
           , MRPat
           , m (MExp m)
           , m (MRBranch m)
           , m (MREnv m)))
    findFirstMatchB env v0 heads mbalts oenv = do
      balts <- mbalts
      case balts of
        Nil    -- do
                       ->
          -- liftIO $ putStrLn $ "cannnot find match branch"
          return Nothing
        Cons mpgb rest -> do
          (p, g, b) <- mpgb
          res <- findMatch p v0
          case res of
            Nothing   -> findFirstMatchB
              env
              v0
              (cons (return (p, g, b)) heads)
              rest
              oenv
            Just bind -> do
              bind
                <- share bind -- bindは後に複数回使われるのでshare
              env' <- share (E.insertAll bind env)
              g'' <- convertRB $ evalU (E.insertAll env' oenv) =<< g
              if g''
                then return $ Just (heads, p, g, b, bind)
                else findFirstMatchB
                  env
                  v0
                  (cons (return (p, g, b)) heads)
                  rest
                  oenv

    -- headsにマッチするものがないことを確かめる
    nomatch :: (MonadPlus m, Sharing m, MonadFail m)
            => m (MREnv m)
            -> MRExp m
            -> m (List m (MRBAlt m))
            -> m (MREnv m)
            -> m Bool
    nomatch env v0 heads oenv = do
      result <- findFirstMatchB env v0 nil heads oenv
      case result of
        Nothing -> return True
        Just _  -> do
          -- liftIO $ putStrLn "nomatch fail"
          return False

    doReconcile :: (MonadPlus m, Sharing m, MonadFail m)
                => m (MREnv m)
                -> Loc
                -> MRExp m
                -> m (MRExp m)
                -> MRExp m
                -> m (List m (MRBAlt m))
                -> m (MREnv m)
                -> m (Store m)
    doReconcile env start v e0 v0 obalts oenv = do
      ((p, g, mb), heads) <- findMatchSW v nil =<< obalts
      heads <- share heads
      b <- mb
      reconcil <- mrReconciler b
      mu0_ <- share $ appR reconcil v0
      u0_ <- mu0_
      mu0 <- share $ appR u0_ v
      u0 <- mu0
      res <- findMatch p u0
      case res of
        Nothing   -> do
          -- liftIO $ putStrLn "Err: switched new source doesn't match!"
          mzero
        Just bind -> do
          bind <- share bind
          env' <- share (E.insertAll bind env)
          True <- nomatch env u0 heads oenv
          g'' <- convertRB $ evalU (E.insertAll env' oenv) =<< g
          if g''
            then putE0 env bind start v e0 oenv p g heads =<< mrBody b
            else do
              -- liftIO $ putStrLn "Err: switched new source doesn't match guard!"
              mzero

    -- どのBranchにswitchするか決める
    findMatchSW
      :: (MonadPlus m, Sharing m, MonadFail m)
      => MRExp m
      -> m (List m (MRBAlt m)) -- 最初に呼ぶときはnilを渡すこと
      -> List m (MRBAlt m)
      -> m (MRBAlt m, m (List m (MRBAlt m)))
    findMatchSW _ heads Nil = mzero -- よいswitch先が見つからない
    findMatchSW v heads (Cons mpgb rest) = do
      (p, g, b) <- mpgb
      exit <- mrExitCond =<< b -- すでにshareされている
      exit' <- convertRB $ appR exit v
      if exit'
        then return ((p, g, b), heads)
        else findMatchSW v (cons (return (p, g, b)) heads) =<< rest

    isMatch :: (MonadPlus m, Sharing m, MonadFail m)
            => m (MREnv m)
            -> m (MREnv m)
            -> MRPat
            -> m (MExp m)
            -> MRExp m
            -> m Bool
    isMatch env oenv p g v0 = do
      res <- findMatch p v0
      case res of
        Nothing   -> do
          -- liftIO $ putStrLn "Err: updated source doesn't match!"
          false
        Just bind -> do
          env' <- share (E.insertAll bind env)
          g'' <- convertRB $ evalU (E.insertAll env' oenv) =<< g
          if g''
            then true
            else do
              -- liftIO $ putStrLn "Err: updated source doesn't match! (guard)"
              false

    putE0 :: (MonadPlus m, Sharing m, MonadFail m)
          => m (MREnv m)
          -> m (MREnv m)
          -> Loc
          -> MRExp m
          -> m (MRExp m)
          -> m (MREnv m)
          -> MRPat
          -> m (MExp m)
          -> m (List m (MRBAlt m))
          -> MExp m
          -> m (Store m)
    putE0 mu bind start v me0 oenv pat g heads body = do
      let next = start + 100
      oenv' <- share oenv'_
      body' <- share $ evalU oenv' body
      muPmui <- share muPmui_
      muPmui' <- share $ evalP_ muPmui next v =<< body'
      (mu', mui') <- S.split start next muPmui'
      mu' <- share mu'
      mui' <- share mui'
      renameEnv <- share renameEnv_
      mv0' <- share $ subP renameEnv pat mui' mui
      v0' <- mv0'
      e0 <- me0
      mu0' <- share $ evalP_ mu start v0' e0
      mu'' <- share $ E.insertAll (convert =<< mu0') mu
      mv0'' <- share $ evalG mu'' start e0
      v0'' <- mv0''
      True <- nomatch mu'' v0'' heads oenv
      True <- isMatch mu'' oenv pat g v0''
      S.merge eqRExp mu0' mu'
      where
        oenv'_ = E.insertAll'
          (map2ML
             (\i mkv -> do
                (x, _) <- mkv
                return (x, return $ MRVar False (return (NameI i))))
             [start ..]
             (E.toList bind))
          oenv

        muPmui_ = E.insertAll'
          (map2ML
             (\i mkv -> do
                (_, v) <- mkv
                return (NameI i, v))
             [start ..]
             (E.toList bind))
          mu

        renameEnv_ = map2ML
          (\i mkv -> do
             (x, _) <- mkv
             return (x, i))
          [start ..]
          (E.toList bind)

        -- mui :: m (Store m)
        mui = S.map2ML_
          (\i mkv -> do
             (_, v) <- mkv
             return (i, v))
          [start ..]
          (E.toList bind)

        subP :: MonadFail m
             => m (List m (Name, Loc))
             -> MRPat
             -> m (Store m)
             -> m (Store m)
             -> m (MRExp m)
        subP rename pat mui' mui = case pat of
          PNum i         -> return $ MRNum False (return i)
          PChar c        -> return $ MRChar False (return c)
          PVar x         -> do
            i <- lookup x rename
            Just e <- S.lookupUpd i mui' mui
            e
          PCon name pats -> return
            $ MRCon False false (return name)
            $ foldr (\pat l -> cons (subP rename pat mui' mui) l) nil pats
          where
            lookup :: Monad m => Name -> m (List m (Name, Loc)) -> m Loc
            lookup name menv = do
              env <- menv
              case env of
                Cons mkv rest -> do
                  (x, i) <- mkv
                  if x == name
                    then return i
                    else lookup name rest

put :: (MonadPlus m, Sharing m, MonadFail m)
    => m (MREnv m)
    -> m (MExp m)
    -> Value
    -> Value
    -> m (MValue m)
put env e s v = do
  let x = NameI (-1)
  env <- share env
  e' <- share $ return (MEApp False e (return (MEVar False (return x))))
  eU <- share
    $ evalU env
    =<< e' -- evalUはenvとeどちらもshare済みでないといけない 
  env2 <- share $ E.insert x (convert s) E.empty
  v' <- share $ convert v
  mu' <- share $ evalP env2 initLoc v' eU
  Just s' <- S.lookupUpd (-1) mu' (S.insert (-1) (convert s) S.empty)
  conv s'
  where
    conv me = do
      e <- me
      case e of
        MRNum _ i          -> return $ MVNum False i
        MRChar _ i         -> return $ MVChar False i
        MRCon _ mb name es -> do
          False <- mb
          return $ MVCon False name (mapML conv es)

-- TD.TExp はちゃんとできるところまでreduceされているものと仮定
-- TD.TExp は f x = ... という相互再帰再帰関数のみを想定 
-- (一応、f = v にも対応
--  v := i, v := c, v := C bool vs, v := !v)
-- LExpはEnvironmentなしでValueまでReduceできるものを仮定
putTest :: [(Name, TD.TExp)] -> Name -> LExp -> LExp -> EV.Env -> IO [Value]
putTest fs f s v ev = resultListIO
  ((do
      let env = initEnv fs -- LazyEvalGetと同じ
      case EV.evalAsUsual s ev of
        Bad str -> fail str
        Ok s'   -> case EV.evalAsUsual v ev of
          Bad str -> fail str
          Ok v'   -> put env (return (MEVar False (return f))) s' v')
   >>= convert)

instance (Monad m, Shareable m c) => Shareable m (Name, Loc, m c) where
  shareArgs f (a, b, c) = do
    c' <- f c
    return (a, b, c')

instance Monad m => Convertible m (Store m) (MREnv m) where
  convert S.Nil = E.empty
  convert (S.Cons _ iv rest) = do
    (i, v) <- iv
    E.insert (NameI i) v (convert =<< rest)

instance Monad m => Shareable m (Name, Loc) where
  shareArgs f (a, b) = return (a, b)
