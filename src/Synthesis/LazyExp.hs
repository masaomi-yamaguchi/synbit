{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wunused-imports #-}

module Synthesis.LazyExp where

import qualified Syntax.Type as T
import           Control.Monad.Sharing
import           Data.Monadic.List
import           EnvLike as E
import           Name
import qualified Typing as TP
import qualified Synthesis.PureExpression as P
import           Synthesis.BxTyping
import           Data.Monadic.Util ()
import qualified Synthesis.LazyEnv as LE
import           DataDecl

type MTyEnv m = LE.Env m Name (MTy m)

data MExp m =
    MEVar Bool (m Name)
  | MEAbs Bool (m Name) (m (MExp m))
  | MEApp Bool (m (MExp m)) (m (MExp m))
  | MEAdd Bool (m (MExp m)) (m (MExp m))
  | MEEq Bool (m (MExp m)) (m (MExp m))
    -- | MELess (m (MExp m)) (m (MExp m))
  | MENeg Bool (m (MExp m))
  | MENum Bool (m Integer)
  | MEChar Bool (m Char)
  | MELift Bool (m (MExp m)) (m (MExp m))
    -- | MEAbort (m (MExp m))
  | MECon Bool (m Bool) (m Name) (m (List m (MExp m))) -- BoolはBXかどうかを表す．nameがNTupのとき，Tupleを表す. ユーザ定義の型もnameで管理している
  | MECase Bool (m (MExp m)) (m (List m (MAlt m)))
  | MECaseB Bool (m (MExp m)) (m (List m (MBAlt m)))
  | MEConstL Bool (m (MExp m)) -- !e のこと
  | MEHole Bool (m (MTy m)) (m (SnEnv m))
  | MEHoleUP Bool P.Pat (m (MTy m)) (m (SnEnv m))
  | MEHoleApp Bool (m (MTy m)) (m (SnEnv m))

type MAlt m = (MPat, m (MGuard m), m (MExp m))

type MBAlt m = (MPat, m (MGuard m), m (MBranch m))

type MGuard m = MExp m

data MBranch m = MBranch { mBody :: m (MExp m)
                         , mExitCond :: m (MExp m)
                         , mReconciler :: m (MExp m)
                         }

-- patternは生成前に確定している
type MPat = P.Pat

-- qeMExp :: Monad m => MExp m -> MExp m -> m Bool
eqMExp :: Monad m => MExp m -> MExp m -> m Bool
eqMExp (MEVar _ mx) (MEVar _ my) = do
  x <- mx
  y <- my
  return (x == y)
eqMExp (MEAbs _ mname1 me1) (MEAbs _ mname2 me2) = do
  name1 <- mname1
  name2 <- mname2
  e1 <- me1
  e2 <- me2
  if name1 == name2
    then eqMExp e1 e2
    else return False
eqMExp (MEApp _ me1 me1') (MEApp _ me2 me2') = do
  e1 <- me1
  e2 <- me2
  b <- eqMExp e1 e2
  if b
    then do
      e1' <- me1'
      e2' <- me2'
      eqMExp e1' e2'
    else return False
eqMExp (MEAdd _ me1 me1') (MEAdd _ me2 me2') = do
  e1 <- me1
  e2 <- me2
  b <- eqMExp e1 e2
  if b
    then do
      e1' <- me1'
      e2' <- me2'
      eqMExp e1' e2'
    else return False
eqMExp (MEEq _ me1 me1') (MEEq _ me2 me2') = do
  e1 <- me1
  e2 <- me2
  b <- eqMExp e1 e2
  if b
    then do
      e1' <- me1'
      e2' <- me2'
      eqMExp e1' e2'
    else return False
eqMExp (MENeg _ me1) (MENeg _ me2) = do
  e1 <- me1
  e2 <- me2
  eqMExp e1 e2
eqMExp (MENum _ mn1) (MENum _ mn2) = do
  n1 <- mn1
  n2 <- mn2
  return (n1 == n2)
eqMExp (MEChar _ mc1) (MEChar _ mc2) = do
  c1 <- mc1
  c2 <- mc2
  return (c1 == c2)
eqMExp (MEConstL _ me1) (MEConstL _ me2) = do
  e1 <- me1
  e2 <- me2
  eqMExp e1 e2
eqMExp (MECon _ mb1 mname1 l1) (MECon _ mb2 mname2 l2) =do
  name1 <- mname1
  name2 <- mname2
  if name1 == name2 then
   do
    b1 <- mb1
    b2 <- mb2
    if b1 == b2
      then do
        and2ML l1 l2
      else return False
  else return False
  where
    and2ML :: Monad m => m (List m (MExp m)) -> m (List m (MExp m)) -> m Bool
    and2ML ml1 ml2 = do
      l1 <- ml1
      l2 <- ml2
      case (l1,l2) of
        (Nil,Nil) -> return True
        (Cons me1 l1', Cons me2 l2') -> do
          e1 <- me1
          e2 <- me2
          b <- eqMExp e1 e2
          if b then and2ML l1' l2'
          else return False

eqMExp _ _ = return False

mTrue :: Monad m => m (MExp m)
mTrue = return $ MECon False (return False) (return NTrue) nil

mFalse :: Monad m => m (MExp m)
mFalse = return $ MECon False (return False) (return NFalse) nil

instance Monad m => Convertible m (MExp m) P.Exp where
  convert (MEVar _ mx) = P.EVar <$> mx
  convert (MEAbs _ mx me) = do
    x <- mx
    e <- me
    e' <- convert e
    return (P.EAbs x e')
  convert (MEApp _ me1 me2) = do
    e1 <- me1
    e2 <- me2
    e1' <- convert e1
    e2' <- convert e2
    return (P.EApp e1' e2')
  convert (MEAdd _ me1 me2) = do
    e1 <- me1
    e2 <- me2
    e1' <- convert e1
    e2' <- convert e2
    return (P.EAdd e1' e2')
  convert (MEEq _ me1 me2) = do
    e1 <- me1
    e2 <- me2
    e1' <- convert e1
    e2' <- convert e2
    return (P.EEq e1' e2')
  -- convert (MELess me1 me2) = do
  --   e1 <- me1
  --   e2 <- me2
  --   e1' <- convert e1
  --   e2' <- convert e2
  --   return (P.ELess e1' e2')
  convert (MENeg _ me) = do
    e <- me
    e' <- convert e
    return (P.ENeg e')
  convert (MENum _ mn) = P.ENum <$> mn
  convert (MEChar _ mc) = P.EChar <$> mc
  convert (MELift _ me1 me2) = do
    e1 <- me1
    e2 <- me2
    e1' <- convert e1
    e2' <- convert e2
    return (P.ELift e1' e2')
  -- convert (MEAbort me) = do
  --   e <- me
  --   e' <- convert e
  --   return (P.EAbort e')
  convert (MECon _ mb mname mes) = do
    es <- mes
    es' <- convert es
    b <- mb
    name <- mname
    return (P.ECon b name es')
  convert (MECase _ me malts) = do
    e <- me
    alts <- malts
    e' <- convert e
    alts' <- convert alts
    return (P.ECase e' alts')
  convert (MECaseB _ me mbalts) = do
    e <- me
    balts <- mbalts
    e' <- convert e
    balts' <- convert balts
    return (P.ECaseB e' balts')
  convert (MEConstL _ me) = do
    e <- me
    e' <- convert e
    return (P.EConstL e')
  convert (MEHole _ mty menv) = do
    env <- menv
    hole' <- convert env
    ty <- mty
    ty' <- convert ty
    return (P.EHole ty' hole')
  convert (MEHoleApp _ mty menv) = do
    env <- menv
    hole' <- convert env
    ty <- mty
    ty' <- convert ty
    return (P.EHole ty' hole')
  convert (MEHoleUP _ _ mty menv) = do
    env <- menv
    hole' <- convert env
    ty <- mty
    ty' <- convert ty
    return (P.EHole ty' hole')

instance Monad m => Convertible m (SnEnv m) (TP.TyEnv, TP.Synonyms) where
  convert SnEnv { tyEnv = tyEn, localEnvM = localEn } = do
    localEn' <- convertMTyEnv localEn
    return $ (E.insertAll (localEn' :: TP.TyEnv) tyEn, TP.defaultSynonyms)
    where
      convertMTyEnv :: Monad m => m (MTyEnv m) -> m TP.TyEnv
      convertMTyEnv env = convert =<< LE.toList env

instance Monad m => Convertible m (List m (Name, m (MTy m))) TP.TyEnv where
  convert Nil = return E.empty
  convert (Cons mkv mrest) = do
    (k, mv) <- mkv
    rest <- mrest
    rest' <- convert rest
    v <- mv
    v' <- convert v
    return $ E.insert k v' rest'

instance Monad m => Convertible m (Name, T.Ty) (Name, m (MTy m)) where
  convert (name, ty) = return (name, convert ty)

instance Monad m => Convertible m (MAlt m) P.Alt where
  convert (pat, mguard, me) = do
    guard <- mguard
    e <- me
    guard' <- convert guard
    e' <- convert e
    return (pat, guard', e')

instance Monad m => Convertible m (MBAlt m) P.BAlt where
  convert (pat, mguard, mbranch) = do
    guard <- mguard
    branch <- mbranch
    guard' <- convert guard
    branch' <- convert branch
    return (pat, guard', branch')

instance Monad m => Convertible m (MBranch m) P.Branch where
  convert branch = do
    body <- mBody branch
    exitCond <- mExitCond branch
    reconciler <- mReconciler branch
    body' <- convert body
    exitCond' <- convert exitCond
    reconciler' <- convert reconciler
    return (P.Branch body' exitCond' reconciler')

instance Monad m => Shareable m (MExp m) where
  shareArgs f (MEVar b x) =
    if b
    then return (MEVar True x)
    else do
      x' <- f x
      return (MEVar True x')
  shareArgs f (MEAbs b x e) =
    if b
    then return (MEAbs True x e)
    else do
      e' <- f e
      return (MEAbs True x e')
  shareArgs f (MEApp b e1 e2) =
    if b
    then return (MEApp True e1 e2)
    else do
      e1' <- f e1
      e2' <- f e2
      return (MEApp True e1' e2')
  shareArgs f (MEAdd b e1 e2) =
    if b
    then return (MEAdd True e1 e2)
    else do
      e1' <- f e1
      e2' <- f e2
      return (MEAdd True e1' e2')
  shareArgs f (MEEq b e1 e2) =
    if b
    then return (MEEq True e1 e2)
    else do
      e1' <- f e1
      e2' <- f e2
      return (MEEq True e1' e2')
  -- shareArgs f (MELess e1 e2) = do
  --   e1' <- f e1
  --   e2' <- f e2
  --   return (MELess e1' e2')
  shareArgs f (MENeg b e) =
    if b
    then return (MENeg True e)
    else do
      e' <- f e
      return (MENeg True e')
  shareArgs f (MENum b n) =
    if b
    then return (MENum True n)
    else do
      n' <- f n
      return (MENum True n')
  shareArgs f (MEChar b c) =
    if b
    then return (MEChar True c)
    else do
      c' <- f c
      return (MEChar True c')
  shareArgs f (MELift b e1 e2) =
    if b
    then return (MELift True e1 e2)
    else do
      e1' <- f e1
      e2' <- f e2
      return (MELift True e1' e2')
  -- shareArgs f (MEAbort e) = do
  --   e' <- f e
  --   return (MEAbort e')
  shareArgs f (MECon bb b n es) =
    if bb
    then return (MECon True b n es)
    else do
      b' <- f b
      n' <- f n
      es' <- f es
      return (MECon True b' n' es')
  shareArgs f (MECase b e alts) =
    if b
    then return (MECase b e alts)
    else do
      e' <- f e
      alts' <- f alts
      return (MECase True e' alts')
  shareArgs f (MECaseB b e balts) =
    if b
    then return (MECaseB b e balts)
    else do
      e' <- f e
      balts' <- f balts
      return (MECaseB True e' balts')
  shareArgs f (MEConstL b e) =
    if b
    then return (MEConstL True e)
    else do
      e' <- f e
      return (MEConstL True e')
  shareArgs f (MEHole b mty hole) =
    if b
    then return (MEHole True mty hole)
    else do
      mty' <- f mty
      hole' <- f hole
      return (MEHole True mty' hole')
  shareArgs f (MEHoleApp b mty hole) =
    if b
    then return (MEHoleApp True mty hole)
    else do
      mty' <- f mty
      hole' <- f hole
      return (MEHoleApp True mty' hole')
  shareArgs f (MEHoleUP b p mty hole) =
    if b
    then return (MEHoleUP True p mty hole)
    else do
      mty' <- f mty
      hole' <- f hole
      return (MEHoleUP True p mty' hole')

instance Monad m => Shareable m (SnEnv m) where
  shareArgs f env = do
    mLocalEn' <- f (localEnvM env)
    return env { localEnvM = mLocalEn' }

instance Monad m => Shareable m (MAlt m) where
  shareArgs f (pat, g, e) = do
    g' <- f g
    e' <- f e
    return (pat, g', e')

instance Monad m => Shareable m (MBAlt m) where
  shareArgs f (pat, g, branch) = do
    g' <- f g
    branch' <- f branch
    return (pat, g', branch')

instance Monad m => Shareable m (Name, m (MExp m), m (MTy m)) where
  shareArgs f (name, me, mty) = do
    me' <- f me
    mty' <- f mty
    return (name, me', mty')

instance Monad m => Shareable m (MBranch m) where
  shareArgs f branch = do
    body' <- f (mBody branch)
    exitCond' <- f (mExitCond branch)
    reconciler' <- f (mReconciler branch)
    return
      $ MBranch { mBody = body'
                , mExitCond = exitCond'
                , mReconciler = reconciler'
                }

type BxTy = T.Ty

type PolyTyEnv = TP.TyEnv

type MonoTyEnv = TP.TyEnv

data SnEnv m =
  SnEnv { tyEnv :: PolyTyEnv
        , usedNames :: [Name]
        , localEnvM :: m (MTyEnv m)
        , dataEnv :: DataEnv
        , pend :: Int
          -- , strEnv_ :: [String]
          -- , charEnv_ :: [Char]
        , canUseAND_ :: Bool
        , canUseOR_ :: Bool
        , canUseNOT_ :: Bool
        , frame_default :: Bool
        , loc_ :: Int
        }
-- convertEnv :: SnEnv m -> IO TP.TcEnv
-- convertEnv env = do
--   ref <- newIORef (0 :: Int)
--   return
--     $ TP.TcEnv { TP.tcUniqRef = ref
--                , TP.tcTyEnv = tyEnv env
--                , TP.tcBxTyEnv = E.empty
--                , TP.tcSynonyms = synonyms env
--                }
