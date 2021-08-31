{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- {-# OPTIONS_GHC -Wunused-imports #-}
-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Synthesis.LazyEvalPTraceNoWith where

import           Value hiding (Store)
import           Control.Monad.Sharing
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
import qualified Eval as EV (evalAsUsual, defaultEnv)
import           Err
import           Synthesis.LazyEvalU
import           Synthesis.LazyEvalG
import           Control.Monad.Fail (MonadFail)
import           Synthesis.LazyEvalP
import           Synthesis.Trace

-- env, mv, meはshareされていることを仮定
evalPTrace :: (MonadPlus m, Sharing m, MonadFail m)
           => m (MREnv m)
           -> Loc
           -> m (MRExp m)
           -> m (MRExp m)
           -> m (MTrace m)
           -> m (Store m)
evalPTrace env start mv me mtrace = do
  v <- mv
  e <- me
  trace <- mtrace
  evalPTrace_ env start v e trace

-- env, v, mexp, MTraceはshareされていることを仮定
evalPTrace_ :: (MonadPlus m, Sharing m, MonadFail m)
            => m (MREnv m)
            -> Loc
            -> MRExp m
            -> MRExp m
            -> MTrace m
            -> m (Store m)
evalPTrace_ env start v (MRVar _ mx) (MTrNil) = do
  x <- mx
  case x of
    NameI i -> S.insert i (return v) S.empty
evalPTrace_
  env
  start
  (MRCon _ vb mvname vs)
  (MRCon _ eb mename es)
  (MTrCon _ muname ub trs) = do
  False <- vb -- Value は bidirectional ではない
  True <- eb -- Residual Exp は bidirectional
  True <- ub
  vname <- mvname
  ename <- mename
  uname <- muname
  if vname == ename && vname == uname
    then go vs es trs
    else do
      -- liftIO $ putStrLn "Err: Update on constant."
      mzero
  where
    go mvs mes mtrs = do
      vs <- mvs
      es <- mes
      trs <- mtrs
      case (vs, es, trs) of
        (Nil, Nil, Nil) -> S.empty
        (Cons v rest1, Cons e rest2, Cons tr rest3) -> do
          mu1 <- share (evalPTrace env start v e tr)
          mu2 <- share (go rest1 rest2 rest3)
          S.merge eqRExp mu1 mu2
evalPTrace_ env start v (MRConstL _ e) MTrConstL = do
  v' <- share $ evalG env start =<< e
  b <- eqRExp v =<< v'
  if b
    then S.empty
    else do
      mzero
evalPTrace_ env start v (MRCaseB _ e0 balts oenv) (MTrBranch _ tr0 chose tr) = do
  mv0 <- share $ evalG env start =<< e0
  v0 <- mv0
  evalBAltsP env start v e0 v0 balts balts oenv (MTrBranch False tr0 chose tr)
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
               -> MTrace m
               -> m (Store m)
    evalBAltsP env start v e0 v0 obalts mbalts oenv (MTrBranch _ tr0 mchose tr) =
      do
        Just (heads, p, g, mb, bind, i)
          <- findFirstMatchB 0 env v0 nil mbalts oenv -- heads以外はshareされている。headsは後に1回しか使われないので無問題
        -- orig <- morig
        -- guard (i == orig)
        b <- mb
        -- exit <- mrExitCond b
        -- exit' <- convertRB $ appR exit v
        chose <- mchose
        if chose == i
          then do
            -- chose <- mchose
            -- guard (chose == i)
            body <- mrBody b
            putE0 env bind start v e0 tr0 oenv p g heads body tr
          else doReconcile env start v e0 tr0 v0 obalts oenv tr chose

    findFirstMatchB
      :: (MonadPlus m, Sharing m, MonadFail m)
      => Int
      -> m (MREnv m)
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
           , m (MREnv m)
           , Int))
    findFirstMatchB i env v0 heads mbalts oenv = do
      balts <- mbalts
      case balts of
        Nil -> return Nothing
        Cons mpgb rest -> do
          (p, g, b) <- mpgb
          res <- findMatch p v0
          case res of
            Nothing   -> findFirstMatchB
              (i + 1)
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
                then return $ Just (heads, p, g, b, bind, i)
                else findFirstMatchB
                  (i + 1)
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
      result <- findFirstMatchB 0 env v0 nil heads oenv
      case result of
        Nothing -> return True
        Just _  -> do
          -- liftIO $ putStrLn "nomatch fail"
          return False

    doReconcile
      :: (MonadPlus m, Sharing m, MonadFail m)
      => m (MREnv m)
      -> Loc
      -> MRExp m
      -> m (MRExp m)
      -> m (MTrace m)
      -> MRExp m
      -> m (List m (MRBAlt m))
      -> m (MREnv m)
      -> m (MTrace m)
      -> Int
      -> m (Store m)
    doReconcile env start v e0 tr0 v0 obalts oenv tr chose = do
      ((p, g, mb), heads) <- findMatchSW chose v nil =<< obalts
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
            then do
              body <- mrBody b
              putE0 env bind start v e0 tr0 oenv p g heads body tr
            else do
              -- liftIO $ putStrLn "Err: switched new source doesn't match guard!"
              mzero

    -- どのBranchにswitchするか決める
    findMatchSW
      :: (MonadPlus m, Sharing m, MonadFail m)
      => Int
      -> MRExp m
      -> m (List m (MRBAlt m)) -- 最初に呼ぶときはnilを渡すこと
      -> List m (MRBAlt m)
      -> m (MRBAlt m, m (List m (MRBAlt m)))
    findMatchSW 0 v heads (Cons mpgb rest) = do
      (p, g, b) <- mpgb
      return ((p, g, b), heads) -- よいswitch先が見つからない
    findMatchSW i v heads (Cons mpgb rest) =
      findMatchSW (i - 1) v (cons mpgb heads) =<< rest

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
          -> m (MTrace m)
          -> m (MREnv m)
          -> MRPat
          -> m (MExp m)
          -> m (List m (MRBAlt m))
          -> MExp m
          -> m (MTrace m)
          -> m (Store m)
    putE0 mu bind start v me0 mtr0 oenv pat g heads body mtr = do
      let next = start + 100
      oenv' <- share oenv'_
      mbody' <- share $ evalU oenv' body
      body' <- mbody'
      muPmui <- share muPmui_
      tr <- mtr
      muPmui' <- share $ evalPTrace_ muPmui next v body' tr
      (mu', mui') <- S.split start next muPmui'
      mu' <- share mu'
      mui' <- share mui'
      renameEnv <- share renameEnv_
      mv0' <- share $ subP renameEnv pat mui' mui
      v0' <- mv0'
      e0 <- me0
      tr0 <- mtr0
      mu0' <- share $ evalPTrace_ mu start v0' e0 tr0
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

putTrace :: (MonadPlus m, Sharing m, MonadFail m)
         => m (MREnv m)
         -> m (MExp m)
         -> Value
         -> Value
         -> m (MTrace m)
         -> m (MValue m)
putTrace env e s v tr = do
  let x = NameI (-1)
  env <- share env
  e' <- share $ return (MEApp False e (return (MEVar False (return x))))
  eU <- share
    $ evalU env
    =<< e' -- evalUはenvとeどちらもshare済みでないといけない
  ms <- share $ convert s
  env2 <- share $ E.insert x ms E.empty
  v' <- share $ convert v
  mu' <- share $ evalPTrace env2 initLoc v' eU tr
  Just s' <- S.lookupUpd (-1) mu' (S.insert (-1) ms S.empty)
  conv s'
  where
    conv me = do
      e <- me
      case e of
        MRNum _ i -> return $ MVNum False i
        MRChar _ i -> return $ MVChar False i
        MRCon _ mb name es -> do
          False <- mb
          return $ MVCon False name (mapML conv es)
        _ -> mzero -- ?? いいのか?

putTraceCheck :: (MonadPlus m, Sharing m, MonadFail m)
              => m (MREnv m)
              -> m (MExp m)
              -> Value
              -> Value
              -> Value
              -> m (MTrace m)
              -> m ()
putTraceCheck env e s v s' tr = guard =<< equalVM s' (putTrace env e s v tr)
-- TD.TExp はちゃんとできるところまでreduceされているものと仮定
-- TD.TExp は f x = ... という相互再帰再帰関数のみを想定 
-- (一応、f = v にも対応
--  v := i, v := c, v := C bool vs, v := !v)
-- LExpはEnvironmentなしでValueまでReduceできるものを仮定
-- putTraceTest :: [(Name, TD.TExp)] -> Name -> LExp -> LExp -> IO [Value]
-- putTraceTest fs f s v = resultList
--   ((do
--       let env = initEnv fs -- LazyEvalGetと同じ
--       case EV.evalAsUsual s EV.defaultEnv of
--         Bad str -> fail str
--         Ok s'   -> case EV.evalAsUsual v EV.defaultEnv of
--           Bad str -> fail str
--           Ok v'   -> putTrace env (return (MEVar (return f))) s' v')
--    >>= convert)
