{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wunused-imports #-}

-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Synthesis.LazyEvalG where

import           Value
import           Control.Monad.Sharing
import           Synthesis.LazyExp
import           Data.Monadic.List
import           Data.Monadic.MBool
import           Synthesis.LazyValue
import           Synthesis.ResidualExp
import           Synthesis.LazyEnv as E hiding (all)
import           Control.Monad
import           Name
import qualified Syntax.Typed as TD
import           Syntax.Type (LExp)
import           Data.List (partition)
import qualified Eval as EV (evalAsUsual, defaultEnv, Env)
import           Err
import           Synthesis.LazyEvalU
import           Control.Monad.Fail (MonadFail)
-- import           Synthesis.LazyEvalG (Loc, initLoc)
import           Synthesis.Trace
import qualified Debug.Trace as DT

type Loc = Int

initLoc :: Loc
initLoc = 0

-- evalG _ _ e = do
--   e' <- convert e
--   trace (show (e' :: Exp)) mzero
-- 非決定的なexpressionを受け取って、
-- 各々の計算結果を返す
-- 一回eとenvをshareで固定すれば、後の計算は決定的なので、shareを考えなくてもバグることはない（計算効率を考えると、shareはちゃんと作るべし）
get :: (MonadPlus m, Sharing m, MonadFail m)
    => m (MExp m)
    -> Value
    -> m (MREnv m)
    -> m (MValue m)
get e s env = do
  (v, _) <- getTrace e s env
  v

evalG :: (MonadPlus m, Sharing m, MonadFail m)
      => m (MREnv m)
      -> Loc
      -> MRExp m
      -> m (MRExp m)
evalG env loc e = do
  (v, _) <- evalGTrace env loc e
  v

-- env, expはshareされていることを前提
evalGTrace :: (MonadPlus m, Sharing m, MonadFail m)
           => m (MREnv m)
           -> Loc
           -> MRExp m
           -> m (m (MRExp m), m (MTrace m))
evalGTrace env loc (MRVar _ mx) = do
  x <- mx
  look <- E.lookup x env
  case look of
    Just e  -> return (e, trNil) -- 環境(case* ofのとこ)に入る前に、どこかでTraceがあるはず
    Nothing -> do
      -- liftIO $ putStrLn $ "evalGTrace env (MRVar mx) Err:\n cannnot find " ++ show x
      fail ""
evalGTrace env loc (MRCon _ b name es) = do
  (vs, trs) <- unzipML $ mapML (\e -> evalGTrace env loc =<< e) es
  return (return (MRCon False false name vs), trCon name b trs)
evalGTrace env loc (MRNum _ i) = return (return (MRNum False i), trNil) -- iを保存した方がいいかも
evalGTrace env loc (MRChar _ c) = return (return (MRChar False c), trNil)-- ここは、cを保存した方がいいかも
evalGTrace env loc (MRConstL _ e) = do
  (r, tr) <- evalGTrace env loc =<< e
  return (r, return MTrConstL)-- 実装さぼり
evalGTrace env loc (MRCaseB _ e0 balts oenv) = do
  me0' <- share $ evalGTrace env loc =<< e0
  (me0', tr0) <- me0'
  e0' <- me0'
  (v, i, tr) <- evalBAltsGTrace e0' balts env oenv 0 loc
  return (v, trBranch tr0 i tr)
  where
    -- MTrBranch (m (MTrace m)) (m Int) (m Int) (m (MTrace m))
    evalBAltsGTrace
      :: (MonadPlus m, Sharing m, MonadFail m)
      => MRExp m
      -> m (List m (MRBAlt m))
      -> m (MREnv m)
      -> m (MREnv m)
      -> Int
      -> Loc
      -> m (m (MRExp m), m Int, m (MTrace m))
    evalBAltsGTrace e0 mbalts env oenv i start = do
      balts <- mbalts
      case balts of
        Nil
         -> mzero -- undefined -- 全てのBranchにマッチしなかった時
        Cons mpgb rest -> do
          (p, g, mb) <- mpgb
          res <- findMatch p e0 -- findMatchの結果はenv'でshareされるので、ここではshare不要
          case res of
            Nothing   -> evalBAltsGTrace e0 rest env oenv (i + 1) start
            Just bind -> do
              env_g <- share (insertAll bind env)
              g'' <- convertRB $ evalU (insertAll env_g oenv) =<< g
              if g'' -- guard check
                then do
                  b <- mb
                  exit <- mrExitCond b -- すでにshareされている
                  oenv' <- share
                    $ insertAll'
                      (map2ML
                         (\i mkv -> do
                            (x, _) <- mkv
                            return (x, return $ MRVar False (return (NameI i))))
                         [start ..]
                         (E.toList bind))
                      oenv
                  let body = evalU oenv' =<< mrBody b
                  let next = start + 100
                  env' <- share
                    $ insertAll'
                      (map2ML
                         (\i mkv -> do
                            (_, v) <- mkv
                            return (NameI i, v))
                         [start ..]
                         (E.toList bind))
                      env
                  mret <- share
                    $ evalGTrace env' next
                    =<< body -- こっちはshareが必要
                  (mv, tr) <- mret
                  v <- mv
                  exit' <- convertRB $ appR exit v
                  if exit'
                    then return (return v, return i, tr)
                    else mzero -- exitconditionを満たさないなら実行時エラー
                else evalBAltsGTrace e0 rest env oenv (i + 1) start
evalGTrace _ _ (MRFun _ mname _ _) = do
  name <- mname
  DT.trace ("MRFun" ++ show name) mzero
evalGTrace _ _ (MRMRFun _ _ _ _) = DT.trace "MRMRFun" mzero
evalGTrace _ _ (MRRFun _ _ _ _ _) = DT.trace "MRRFun" mzero

-- 非決定的なexpressionを受け取って、
-- 各々の計算結果を返す
-- 一回eとenvをshareで固定すれば、後の計算は決定的なので、shareを考えなくてもバグることはない（計算効率を考えると、shareはちゃんと作るべし）
getTrace :: (MonadPlus m, Sharing m, MonadFail m)
         => m (MExp m)
         -> Value
         -> m (MREnv m)
         -> m (m (MValue m), m (MTrace m))
getTrace e s env = do
  let x = NameI (-1)
  env <- share env
  e' <- share $ return (MEApp False e (return (MEVar False (return x))))
  eU <- share
    $ evalU env
    =<< e' -- evalUはenvとeどちらもshare済みでないといけない 
  env2 <- share $ insert x (convert s) empty
  (re, tr) <- evalGTrace env2 initLoc
    =<< eU -- evalGはenvとeどちらもshare済みでないといけない
  return (conv re, tr)
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
getTraceTest
  :: [(Name, TD.TExp)] -> Name -> LExp -> EV.Env -> IO [(Value, Trace)]
getTraceTest fs f s ev = resultListIO
  ((do
      let env = initEnv fs -- `mplus` initEnv fs
      case EV.evalAsUsual
        s
        ev   -- ユーザ定義型を許してないけど、testだからOK
         of
          Bad str -> fail str
          Ok s'   -> getTrace (return (MEVar False (return f))) s' env)
   >>= convert)

-- TD.TExp はちゃんとできるところまでreduceされているものと仮定
-- TD.TExp は f x = ... という相互再帰再帰関数のみを想定 
-- (一応、f = v にも対応
--  v := i, v := c, v := C bool vs, v := !v)
-- LExpはEnvironmentなしでValueまでReduceできるものを仮定
getTest :: [(Name, TD.TExp)] -> Name -> LExp -> EV.Env -> IO [Value]
getTest fs f s ev = resultListIO
  ((do
      let env = initEnv fs -- `mplus` initEnv fs
      case EV.evalAsUsual
        s
        ev   -- ユーザ定義型を許してないけど、testだからOK
         of
          Bad str -> fail str
          Ok s'   -> get (return (MEVar False (return f))) s' env)
   >>= convert)

initEnv
  :: (Sharing m, Monad m, MonadFail m) => [(Name, TD.TExp)] -> m (MREnv m)
initEnv l = do
  let (vs, fs) = partition (\(name, e) -> isFO e) l
  env <- share
    $ foldr
      (\(name, e) env -> do
         let e' = convert e
         let e'' = evalU empty =<< e'
         insert name e'' env)
      empty
      vs
  let fs' = (foldr
               (\(f, TD.Typed (TD.EAbs x e) _) l
                -> cons (return (return f, return x, convert e)) l)
               nil
               fs)
  let env' = foldri
        (\(f, _) i l -> insert f (return $ MRMRFun False (return i) fs' env) l)
        env
        fs
  env'
  where
    isFO :: TD.TExp -> Bool
    isFO (TD.Typed (TD.ENum _) _) = True
    isFO (TD.Typed (TD.EChar _) _) = True
    isFO (TD.Typed (TD.ECon b name es) _) = all isFO es
    isFO (TD.Typed (TD.EConstL e) _) = isFO e
    isFO (TD.Typed (TD.EAbs x e) _) = False

    foldri :: (a -> Int -> b -> b) -> b -> [a] -> b
    foldri f = go f 0
      where
        go f i e [] = e
        go f i e (x:xs) = f x i (go f (i + 1) e xs)

instance Monad m => Convertible m TD.TExp (MExp m) where
  convert (TD.Typed (TD.EVar x) _) = return $ MEVar False (return x)
  convert (TD.Typed (TD.EAbs x e) _) = do
    let e' = convert e
    return $ MEAbs False (return x) e'
  convert (TD.Typed (TD.EApp e1 e2) _) = do
    let e1' = convert e1
    let e2' = convert e2
    return $ MEApp False e1' e2'
  convert (TD.Typed (TD.EAdd e1 e2) _) = do
    let e1' = convert e1
    let e2' = convert e2
    return $ MEAdd False e1' e2'
  convert (TD.Typed (TD.EEq e1 e2) _) = do
    let e1' = convert e1
    let e2' = convert e2
    return $ MEEq False e1' e2'
  convert (TD.Typed (TD.ENeg e1) _) = do
    let e1' = convert e1
    return $ MENeg False e1'
  convert (TD.Typed (TD.ENum i) _) = return $ MENum False (return i)
  convert (TD.Typed (TD.EChar c) _) = return $ MEChar False (return c)
  convert (TD.Typed (TD.ECon b name es) _) = do
    let es' = convert es
    return $ MECon False (return b) (return name) es'
  convert (TD.Typed (TD.EConstL e) _) = do
    let e' = convert e
    return $ MEConstL False e'
  convert (TD.Typed (TD.ECase e0 alt) _) = do
    let e0' = convert e0
    let alt' = convert alt
    return $ MECase False e0' alt'
  convert (TD.Typed (TD.ECaseB e0 balt) _) = do
    let e0' = convert e0
    let balt' = convert balt
    return $ MECaseB False e0' balt'

instance Monad m => Convertible m TD.TAlt (MAlt m) where
  convert (pat, g, e) = do
    let g' = convert g
    let e' = convert e
    return (pat, g', e')

instance Monad m => Convertible m TD.TBAlt (MBAlt m) where
  convert (pat, g, TD.TBranch bo ex re) = do
    let g' = convert g
    let bo' = convert bo
    let ex' = convert ex
    let re' = convert re
    let branch' = return $ MBranch bo' ex' re'
    return (pat, g', branch')

-- patternConvert :: TD.Pat -> MPat
-- patternConvert (TD.PNum i) = PNum i
-- patternConvert (TD.PChar c) = PChar c
-- patternConvert (TD.PVar v) = PVar v
-- patternConvert (TD.PCon name l) = PCon name (map patternConvert l)
instance Monad m => Convertible m Value (MRExp m) where
  convert (VNum i) = return $ MRNum False (return i)
  convert (VChar c) = return $ MRChar False (return c)
  convert (VCon name vs) = do
    let es = convert vs
    return $ MRCon False false (return name) es

instance MonadFail m => Convertible m (MRExp m) Value where
  convert (MRNum _ mi) = VNum <$> mi
  convert (MRChar _ mc) = VChar <$> mc
  convert (MRCon _ mb mname mes) = do
    name <- mname
    False <- mb
    es <- mes
    vs <- convert es
    return $ VCon name vs
