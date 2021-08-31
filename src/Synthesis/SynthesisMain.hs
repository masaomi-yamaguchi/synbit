{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- {-# OPTIONS_GHC -Wunused-imports #-}
-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Synthesis.SynthesisMain where

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
import qualified Synthesis.LazyEnv as LE
import qualified Synthesis.LazyStore as S
import           Name
import qualified Typing as TP
import           Synthesis.PureExpression
import qualified Syntax.Typed as TD
import           Data.List (partition)
import qualified Eval as EV (evalAsUsual, defaultEnv)
import           Err
import           Synthesis.LazyEvalU
import           Synthesis.LazyEvalG
import           Control.Monad.Fail (MonadFail)
import           Synthesis.LazyEvalP
import           Synthesis.Trace
import           DataDecl as D
import           Syntax.Typed as TD
import           Synthesis.BxFrame
import           Synthesis.BxTyping
import           Syntax.Type as T
import           Synthesis.GenExp hiding (pen)
import qualified Synthesis.PureExpression as P
import           Control.Applicative
import qualified Synthesis.LazyEvalG as LG
import           Synthesis.LazyEvalPTrace (putTraceCheck)
import qualified Synthesis.LazyEvalPTraceNoWith as LPN (putTraceCheck)
import           Eval (Env)
import qualified EnvLike as E
import qualified Data.Set
import           Debug.Trace as DT
import qualified Synthesis.LazySetOrd as LS

data Example = Example Value Value Value Value
  deriving Show

pen = 100

synthesisMain
  :: TP.TyEnv
  -> TP.Synonyms
  -> DataEnv
  -> UniqSupply
  -> [(Name, TExp)]
  -> (Name, TExp)
  -> [(Name, TExp)]
  -> [Example]
  -> Maybe [(Name, T.Ty, P.Exp)]
synthesisMain tyenv syn denv ref nonBxEnv (f0, e0) nonRoots examples =
  case resultList
    (synthesis tyenv syn denv ref nonBxEnv (f0, e0) nonRoots examples
     >>= convert) of
    []   -> Nothing
    x:xs -> Just x

synthesis :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
          => TP.TyEnv
          -> TP.Synonyms
          -> DataEnv
          -> UniqSupply
          -> [(Name, TExp)]
          -> (Name, TExp)
          -> [(Name, TExp)]
          -> [Example]
          -> m (List m (Name, m (MTy m), m (MExp m)))
synthesis tyenv syn denv ref nonBxEnv (f0, e0) nonRoots examples =
  -- let (ss, cs) = foldr
  --       (\(f, e) l -> obtainStringsChars (convertToPure e) `merge` l)
  --       ([], [])
  --       ((f0, e0):nonRoots)
  let (ss, cs) = ([], [])
      nonBxEnv' = foldr
        (\(f, Typed e ty) env -> case f of
           Name "andAlso" -> env
           Name "orElse" -> env
           Name "not" -> env
           _ -> E.insert f ty env)
        E.empty
        nonBxEnv
  in do
       nonBxEnv''    -- trace (show (frames'' :: [(Name, P.Exp, Ty)])) $
         <- share
         $ convertSnEnvToMTEnv
           nonBxEnv'
           denv -- forallの環境をGenExp用に変換
       env <- share $ LG.initEnv nonBxEnv
       snenv <- share --(initSnEnv tyenv syn denv ref pen nonBxEnv False ss cs)
         $ initSnEnv tyenv syn denv ref pen nonBxEnv True -- ss cs
       frames <- share $ makeFramesAll snenv (f0, e0) nonRoots
       -- frames' <- frames
       -- frames'' <- convert frames'
       filled <- share
         $ mapML
           (\tmp -> do
              (f, e, ty) <- tmp
              return (f, fillHole True pen nonBxEnv'' e))
           frames
       -- (f0e0', nonRots') <- headTail (traceMExps filled)
       (f0e0', nonRots') <- headTail filled
       (f0', e0') <- f0e0'
       fs' <- share
         $ foldrML
           (\fxe l -> do
              (f, mxe) <- fxe
              xe <- mxe
              let MEAbs _ x e = xe
              cons (return (return f, x, e)) l)
           nil
           filled
       env <- share
         $ foldriML
           (\fxe i l -> do
              (f, e) <- fxe
              LE.insert f (return $ MRMRFun False i fs' env) l)
           env
           filled
       checkGet examples e0' env
       checkGetPut examples e0' env
       let tys = mapML -- 結果出力用
             (\tmp -> do
                (f, e, ty) <- tmp
                ty)
             frames
       foldrML2
         (\fe ty l -> do
            (f, e) <- fe
            cons (return (f, ty, e)) l)
         nil
         filled
         tys
  where
    headTail :: Monad m => m (List m a) -> m (m a, m (List m a))
    headTail ml = do
      l <- ml
      case l of
        Cons x xs -> return (x, xs)

    -- obtainStringsChars :: P.Exp -> ([String], [Char])
    -- obtainStringsChars = go
    --   where
    --     go (P.EVar x) = ([], [])
    --     go (P.EAbs x e) = go e
    --     go (P.EApp e1 e2) = go e1 `merge` go e2
    --     go (P.EAdd e1 e2) = go e1 `merge` go e2
    --     go (P.EEq e1 e2) = go e1 `merge` go e2
    --     go (P.ELess e1 e2) = go e1 `merge` go e2
    --     go (P.ENeg e1) = go e1
    --     go (P.ENum i) = ([], [])
    --     go (P.EChar c) = ([], [])
    --     go (P.ELift e1 e2) = go e1 `merge` go e2
    --     go (P.EAbort e1) = go e1
    --     go (P.ECon b name es) = foldr (\e l -> go e `merge` l) ([], []) es
    --     go (P.ECase e0 alts) =
    --       foldr (\alt l -> goAlt alt `merge` l) ([], []) alts
    --       where
    --         goAlt (p, g, e) = convPat p `merge` go g `merge` go e
    --     go (P.ECaseB e0 balts) =
    --       foldr (\alt l -> goBAlt alt `merge` l) ([], []) balts
    --       where
    --         goBAlt (p, g, br) = convPat p
    --           `merge` go g
    --           `merge` go (P.body br)
    --           `merge` go (P.exitCond br)
    --           `merge` go (P.reconciler br)
    --     go (P.EConstL e1) = go e1
    --     convPat :: P.Pat -> ([String], [Char])
    --     convPat (P.PVar x) = ([], [])
    --     convPat (P.PNum i) = ([], [])
    --     convPat (P.PChar c) = ([], [c])
    --     convPat (P.PCon NNil []) = ([], [])
    --     convPat (P.PCon NCons [p1, l]) = case go p1 l of
    --       Just ss -> ([ss], [])
    --       Nothing -> foldr (\p l' -> convPat p `merge` l') ([], []) [p1, l]
    --       where
    --         go :: P.Pat -> P.Pat -> Maybe String
    --         go (P.PChar c) (P.PCon NNil []) = Just [c]
    --         go (P.PChar c) (P.PCon NCons [p', l']) = cons c (go p' l')
    --         go _ _ = Nothing
    --         cons :: Char -> Maybe String -> Maybe String
    --         cons c ms = do
    --           s <- ms
    --           return (c:s)
    --     convPat (P.PCon _ l) = foldr (\p l' -> convPat p `merge` l') ([], []) l
    -- merge :: ([String], [Char]) -> ([String], [Char]) -> ([String], [Char])
    -- merge (s1, c1) (s2, c2) = (insertAll s1 s2, insertAll c1 c2)
    --   where
    --     insert x l = if x `elem` l
    --                  then l
    --                  else x:l
    --     insertAll l1 l2 = foldr insert l2 l1
    -- traceMExps :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
    --            => m (List m (Name, m (MExp m)))
    --            -> m (List m (Name, m (MExp m)))
    -- traceMExps mes = do
    --   mes <- share mes
    --   es <- mes
    --   es' <- convert es
    --   let str = show (es' :: [(Name, P.Exp)])
    --   return (trace str es)
checkGet :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
         => [Example]
         -> m (MExp m)
         -> m (MREnv m)
         -> m ()
checkGet examples e env = mapM_ (\example -> go example e env) examples
  where
    go :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
       => Example
       -> m (MExp m)
       -> m (MREnv m)
       -> m ()
    go (Example s v _ _) e env = do
      (v_, trace) <- LG.getTrace e s env
      eqv <- equalVM v v_
      if eqv
        then return ()
        else mzero

checkGetPut :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
            => [Example]
            -> m (MExp m)
            -> m (MREnv m)
            -> m ()
checkGetPut examples e env = mapM_ (\example -> go example e env) examples
  where
    go :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
       => Example
       -> m (MExp m)
       -> m (MREnv m)
       -> m ()
    go (Example s _ v s') e env = do
      (v_, trace) <- LG.getTrace e s' env
      eqv <- equalVM v v_
      if eqv
        then do
          trace <- share trace
          putTraceCheck env e s v s' trace
        else error
          "Example Err. Updated source must be reduced to updated view"

    --
    -- Trace用
    --
    -- equalVM' :: Monad m => Value -> m (MValue m) -> m Bool
    -- equalVM' v1 mv2 = do
    --   v2 <- convert =<< mv2
    --   return
    --     (equal (trace ("v1 = " ++ show v1) v1) (trace ("v2 = " ++ show v2) v2))
fillHoleTest :: TP.TyEnv
             -> TP.Synonyms
             -> DataEnv
             -> UniqSupply
             -> [(Name, TExp)]
             -> (Name, TExp)
             -> [(Name, TExp)]
             -> IO [[(Name, P.Exp)]]
fillHoleTest tyenv syn denv ref nonBxEnv (f0, e0) nonRoots = resultListIO
  ((do
      snenv <- share $ initSnEnv tyenv syn denv ref pen nonBxEnv False -- [] []
      frames <- share $ makeFramesAll snenv (f0, e0) nonRoots
      let tyenv' =
            foldr (\(f, Typed e ty) env -> E.insert f ty env) E.empty nonBxEnv
      genEnv <- share
        $ convertSnEnvToMTEnv tyenv' denv -- forallの環境をGenExp用に変換
      let filled = mapML
            (\tmp -> do
               (f, e, ty) <- tmp
               return (f, fillHole True pen genEnv e))
            frames
      filled)
   >>= convert)

-- -- 結果用
instance Monad m => Convertible m (Name, m (MExp m)) (Name, P.Exp) where
  convert (name, e) = do
    e' <- convert =<< e
    return (name, e')

instance Monad m
  => Convertible m (Name, m (MExp m), m (MTy m)) (Name, P.Exp, T.Ty) where
  convert (name, e, ty) = do
    e' <- convert =<< e
    ty' <- convert =<< ty
    return (name, e', ty')

instance Monad m
  => Convertible m (Name, m (MTy m), m (MExp m)) (Name, T.Ty, P.Exp) where
  convert (name, ty, e) = do
    e' <- convert =<< e
    ty' <- convert =<< ty
    return (name, ty', e')

fillHole :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
         => Bool --  withを埋めるかどうか
         -> Int
         -> m (MTyEnv m)
         -> m (MExp m)
         -> m (MExp m)
fillHole with_flag pen nonBxEnv me = do
  e <- me
  case e of
    MEVar b x -> return (MEVar False x)
    MEAbs _ x e1 -> return (MEAbs False x (fillHole with_flag pen nonBxEnv e1))
    MEApp _ e1 e2 -> return
      (MEApp
         False
         (fillHole with_flag pen nonBxEnv e1)
         (fillHole with_flag pen nonBxEnv e2))
    MEAdd _ e1 e2 -> return
      (MEAdd
         False
         (fillHole with_flag pen nonBxEnv e1)
         (fillHole with_flag pen nonBxEnv e2))
    MEEq _ e1 e2 -> return
      (MEEq
         False
         (fillHole with_flag pen nonBxEnv e1)
         (fillHole with_flag pen nonBxEnv e2))
    MENeg _ e1 -> return (MENeg False (fillHole with_flag pen nonBxEnv e1))
    MENum _ i -> return (MENum False i)
    MEChar _ c -> return (MEChar False c)
    MELift _ e1 e2 -> return
      (MELift
         False
         (fillHole with_flag pen nonBxEnv e1)
         (fillHole with_flag pen nonBxEnv e2))
    MECon _ b name l -> return
      (MECon False b name (mapML (fillHole with_flag pen nonBxEnv) l))
    MECase _ e1 alts -> return
      (MECase False (fillHole with_flag pen nonBxEnv e1) (goAlt alts))
    MECaseB _ e1 balts -> return
      (MECaseB False (fillHole with_flag pen nonBxEnv e1) (goBAlt balts))
    MEConstL _ e1 -> return
      (MEConstL False (fillHole with_flag pen nonBxEnv e1))
    MEHole _ ty msnenv -> do
      msnenv <- share msnenv
      snenv <- msnenv
      let depth = 100
      vars <- share $ collectTyVar (localEnvM snenv)
      -- depth <- aux 2
      env' <- share (LE.insertAll (localEnvM snenv) nonBxEnv)
      genEnv <- initGenEnv
        (dataEnv snenv)
        (Data.Set.fromList (usedNames snenv))
        pen
        (Loc (loc_ snenv))
        env'
        vars
        -- (strEnv_ snenv)
        -- (charEnv_ snenv)
        (canUseAND_ snenv)
        (canUseOR_ snenv)
        (canUseNOT_ snenv)
      genU Nothing genEnv =<< ty
    MEHoleApp _ ty msnenv -> do
      msnenv <- share msnenv
      snenv <- msnenv
      let depth = 100
      vars <- share $ collectTyVar (localEnvM snenv)
      env' <- share (LE.insertAll (localEnvM snenv) nonBxEnv)
      genEnv <- initGenEnv
        (dataEnv snenv)
        (Data.Set.fromList (usedNames snenv))
        pen
        (Loc (loc_ snenv))
        env'
        vars
        (canUseAND_ snenv)
        (canUseOR_ snenv)
        (canUseNOT_ snenv)
      genExpForHoleApp genEnv =<< ty
    MEHoleUP _ p ty msnenv -> do
      msnenv <- share msnenv
      snenv <- msnenv
      let depth = 100
      vars <- share $ collectTyVar (localEnvM snenv)
      -- depth <- aux 2
      env' <- share (LE.insertAll (localEnvM snenv) nonBxEnv)
      genEnv <- initGenEnv
        (dataEnv snenv)
        (Data.Set.fromList (usedNames snenv))
        pen
        (Loc (loc_ snenv))
        env'
        vars
        -- (strEnv_ snenv)
        -- (charEnv_ snenv)
        (canUseAND_ snenv)
        (canUseOR_ snenv)
        (canUseNOT_ snenv)
      genU (Just p) genEnv =<< ty
  where
    goAlt = mapML
      (\malt -> do
         (p, g, e) <- malt
         return (p, g, fillHole with_flag pen nonBxEnv e))

    goBAlt = mapML
      (\mbalt -> do
         (p, g, mbranch) <- mbalt
         MBranch { mBody = body, mExitCond = exit, mReconciler = recon }
           <- mbranch
         return
           ( p
           , g
           , return
               (MBranch { mBody = fillHole with_flag pen nonBxEnv body
                        , mExitCond = if with_flag
                                      then fillHole with_flag pen nonBxEnv exit
                                      else exit
                        , mReconciler = fillHole with_flag pen nonBxEnv recon
                        })))

    collectTyVar
      :: (MonadPlus m, Delay m, Sharing m) => m (MTyEnv m) -> m (TyVarSet m)
    collectTyVar = LE.foldrE
      (\name ty vars -> do
         go name ty vars)
      LS.empty
      where
        go :: (Monad m, Sharing m, Delay m)
           => Name
           -> m (MTy m)
           -> m (TyVarSet m)
           -> m (TyVarSet m)
        go name mty vs = do
          -- nameはデバッグ用
          ty <- mty
          case ty of
            MTyApp _ _ l -> foldrML (go name) vs l
            MTyVar x           -- trace ("debug: MTyApp" ++ show x)
              -> (LS.add x vs)
            MTyForAll _ abc _ ->
              -- trace
              -- ("debug: " ++ show name ++ " :: MTyForAll" ++ show abc)
              vs
