{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wunused-imports #-}

module Synthesis.BxFrame where

import qualified Syntax.Type as T
import           Control.Monad.Sharing (Delay(..), resultListIO, Convertible(..)
                                      , Shareable(..), Sharing(..))
import           Data.Monadic.List
import           EnvLike as E
import           Name
import           Syntax.Typed as TD
import qualified Typing as TP
import qualified Synthesis.PureExpression as P
import           Synthesis.BxTyping as BT
import           Data.Monadic.Util (UniqSupply)
import           Synthesis.LazyExp
import           Control.Monad.Fail (MonadFail)
import           Control.Monad
import           DataDecl as D
import           Control.Applicative
import qualified Synthesis.LazyEnv as LE
import qualified Debug.Trace as DT

data MTExp m = MTyped (MExp m) (MTy m)

-- 単体テスト用
makeFramesTest :: TP.TyEnv
               -> TP.Synonyms
               -> DataEnv
               -> UniqSupply
               -> Name
               -> TExp
               -> IO [Typed P.Exp]
makeFramesTest env syn denv ref f e = resultListIO
  $ ((do
        mty' <- share $ synthesisB pen (getType e)
        e' <- makeFrames (initSnEnv env syn denv ref pen [] False) False e mty'
        MTyped e' <$> mty')
     >>= convert)
  where
    pen = 100

-- メインの関数
makeFramesAll :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
              => m (SnEnv m)
              -> (Name, TExp)
              -> [(Name, TExp)]
              -> m (List m (Name, m (MExp m), m (MTy m)))
makeFramesAll menv (f0, e0) nonRoots = do
  let (T.TyForAll abc ty0) = getType e0
  (a, b) <- ensureArrowType ty0
  let ty0' = T.TyForAll abc (T.TyArr (T.TyB a) (T.TyB b))
  mty0' <- share $ convert ty0'
  menv <- share menv
  env <- menv
  nonRoots' <- share
    $ foldr
      (\(name, Typed e ty) nonRoots' -> do
         let ty' = synthesisB (pend env) ty
         cons (return (name, Typed e ty, ty')) nonRoots')
      nil
      nonRoots
  snEnv <- share
    $ foldrML
      (\mfety menv' -> do
         (f, e, mty') <- mfety
         extendLocalM f mty' menv')
      (extendLocalM f0 mty0' menv)
      nonRoots'
  let e0'' = makeFrames snEnv False e0 mty0'
  nonRoots'' <- share
    $ mapML
      (\mfety' -> do
         (f, e, mty') <- mfety'
         return (f, makeFrames snEnv False e mty', mty'))
      nonRoots'
  cons (return (f0, e0'', mty0')) nonRoots''

-- メインの関数
makeFramesAllTest
  :: TP.TyEnv
  -> TP.Synonyms
  -> DataEnv
  -> UniqSupply
  -> (Name, TExp)
  -> [(Name, TExp)]
  -> IO [[(Name, Typed P.Exp)]]
makeFramesAllTest env syn denv ref (f0, e0) nonRoots = resultListIO
  (do
     let menv = initSnEnv env syn denv ref pen nonRoots True
     makeFramesAll menv (f0, e0) nonRoots >>= convert)
  where
    pen = 100

instance Monad m => Shareable m (Name, Typed Exp, m (MBxTy m)) where
   -- makeFramesAll専用
  shareArgs f (name, e, mty) = do
    mty' <- f mty
    return (name, e, mty')

instance Monad m
  => Convertible m (Name, m (MExp m), m (MTy m)) (Name, Typed P.Exp) where
  -- makeFramesAll専用
  convert (name, me, mty) = do
    e <- me
    ty <- mty
    e' <- convert e
    ty' <- convert ty
    return (name, Typed e' ty')

instance Monad m => Convertible m (MTExp m) (Typed P.Exp) where
  convert (MTyped me mt) = do
    e <- convert me
    t <- convert mt
    return $ Typed e t

initSnEnv :: (MonadPlus m, Delay m, Sharing m)
          => PolyTyEnv
          -> TP.Synonyms
          -> DataEnv
          -> UniqSupply
          -> Int
          -> [(Name, TExp)]
          -> Bool
          -> m (SnEnv m)
initSnEnv decEnv syn denv ref pen nonBxEnv f_default = return
  $ SnEnv { tyEnv = decEnv
          , usedNames = []
          , localEnvM = LE.empty
          , dataEnv = denv
          , pend = pen
            -- , charEnv_ = charEnv
            -- , strEnv_ = strEnv
          , canUseAND_ = canUse "andAlso"
          , canUseOR_ = canUse "orElse"
          , canUseNOT_ = canUse "not"
          , frame_default = f_default
          , loc_ = 0
          }
  where
    canUse :: String -> Bool
    canUse f = case Prelude.lookup (Name f) nonBxEnv of
      Nothing -> False
      Just _  -> True

convertSnEnvToMTEnv :: Monad m => TP.TyEnv -> DataEnv -> m (MTyEnv m)
convertSnEnvToMTEnv tyenv denv = foldr
  (\(name, ty) env
   -> if name == Name "inspect"
        || name == Name "comp"
        || name == Name "showInt"
        || D.contains denv name
      then env
      else do
        LE.insert name (convert ty) env)
  LE.empty
  (E.toList tyenv)

isBx :: Monad m => m (MTy m) -> m Bool
isBx mty = do
  ty <- mty
  return
    $ case ty of
      MTyApp _ (TName "BX") _ -> True
      _ -> False

ensureArrowType :: Monad m => T.Ty -> m (T.Ty, T.Ty)
ensureArrowType ty = case ty of
  T.TyArr t1 t2 -> return (t1, t2)
  _ -> fail "something happend in ensureArrowType"

extendLocalM :: Monad m => Name -> m (MTy m) -> m (SnEnv m) -> m (SnEnv m)
extendLocalM x t menv = do
  env <- menv
  return $ env { localEnvM = LE.insert x t (localEnvM env) }

extendAllLocalM
  :: Monad m => m (List m (Name, m (MTy m))) -> m (SnEnv m) -> m (SnEnv m)
extendAllLocalM ml menv = do
  l <- ml
  case l of
    Nil           -> menv
    Cons mkv rest -> do
      (k, mv) <- mkv
      extendLocalM k mv (extendAllLocalM rest menv)

ensureArrowType2
  :: MonadFail m => T.Ty -> m (MTy m) -> m (T.Ty, T.Ty, m (MTy m), m (MTy m))
ensureArrowType2 ty mty = do
  bxty <- mty
  case (ty, bxty) of
    (T.TyArr ty1 ty2, MTyApp _ (TName "->") mab) -> do
      Cons mty1 mb <- mab
      Cons mty2 nil <- mb
      return (ty1, ty2, mty1, mty2)

ensureTupTypeM :: Monad m => m (MTy m) -> (m (List m (MTy m)))
ensureTupTypeM mty = do
  ty <- mty
  case ty of
    MTyApp _ (TName "(,..,)") xs -> xs
    _ -> fail "Something happend in ensureTupTypeM!"

lookupTyEnv :: Monad m => Name -> m (SnEnv m) -> m T.Ty
lookupTyEnv name menv = do
  env <- menv
  case E.lookup name (tyEnv env) of
    Nothing -> fail $ "Cannnot find " ++ show name ++ " in lookupTyEnv"
    Just ty -> return ty

makeFrames :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
           => m (SnEnv m)
           -> Bool
           -> TExp
           -> m (MBxTy m)
           -> m (MExp m)
makeFrames menv inBang (Typed e (T.TyForAll abc ty)) mty' = do
  ty' <- mty'
  case ty' of
    (MTyForAll _ abc' mty'') -> makeFrames' menv inBang (Typed e ty) mty''
makeFrames menv inBang e mty = do
  mty <- share $ mty
  ty <- mty
  case ty of
    MTyApp _ (TName "BX") ml -> do
      l <- ml
      case l of
        Cons ty1 _ -> do
          menv <- share menv
          (return $ MEConstL False $ makeFrames' menv True e ty1)
            `mplus` makeFrames' menv inBang e mty
    _ -> makeFrames' menv inBang e mty

makeFrames' :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
            => m (SnEnv m)
            -> Bool
            -> TExp
            -> m (MBxTy m)
            -> m (MExp m)
makeFrames' menv inBang (Typed (EVar x) ty) mmty' = do
  mmty' <- share mmty'
  env <- menv
  look <- LE.lookup x (localEnvM env)
  case look of
    Just mpolyty -> do
      uni <- BT.unifiable mpolyty mmty'
      if uni
        then return (MEVar False (return x))
        else mzero
    Nothing      -> case E.lookup x (tyEnv env) of
      Just polyTy -> do
        uni <- BT.unifiable (convert polyTy) mmty'
        if uni
          then return (MEVar False (return x))
          else mzero
      Nothing
        -> fail $ "cannot find " ++ show x ++ "in EVar x of makeFrames."
makeFrames' menv inBang (Typed (EApp e1 e2) ty) mty1' = do
  menv <- share menv
  env <- menv
  (ty2, ty1) <- ensureArrowType (getType e1)
  mty2' <- share $ synthesisB (pend env) ty2
  let e1' = makeFrames menv inBang e1 (mTyArr mty2' mty1')
  let e2' = makeFrames menv inBang e2 mty2'
  return (MEApp False e1' e2')
makeFrames' menv inBang (Typed (EAbs x e1) ty) mty' = do
  (ty1, ty2, mty1', mty2') <- ensureArrowType2 ty mty'
  let e1' = makeFrames (extendLocalM x mty1' menv) inBang e1 mty2'
  return (MEAbs False (return x) e1')
makeFrames' menv inBang (Typed (ENum i) ty) mty' = do
  isB <- isBx mty'
  if isB
    then mzero -- 2個同じものが生成されてしまうのを防ぐ
    else
      -- then return $ MEConstL (return (MENum (return i)))
      return (MENum False (return i))
makeFrames' menv inBang (Typed (EChar c) ty) mty' = do
  isB <- isBx mty'
  if isB
    then mzero -- return $ MEConstL (return (MEChar (return c)))
    else return (MEChar False (return c))
-- makeFrames' menv inBang (Typed (ECon False NTup es) ty) mty' = do
--   mty' <- share mty'
--   isB <- isBx mty'
--   if isB
--     then do
--       let es' = foldr
--             (\e ml -> do
--                let e' = makeFrames menv inBang e (mTyB (convert (getType e)))
--                cons e' ml)
--             nil
--             es
--       return (MECon (return True) (return NTup) es')
--     else if inBang
--          then mzero
--          else do
--            mtys' <- share $ ensureTupTypeM mty'
--            let es' = map2ML (\e mty' -> makeFrames menv inBang e mty') es mtys'
--            return (MECon (return False) (return NTup) es')
makeFrames' menv inBang (Typed (ECon False name es) ty) mty' = do
  mty' <- share mty'
  isB <- isBx mty'
  if isB
    then do
      let es' = foldr
            (\e ml -> do
               let e' = makeFrames menv inBang e (mTyB (convert (getType e)))
               cons e' ml)
            nil
            es
      return (MECon False (return True) (return name) es')
    else if inBang
         then mzero
         else if name == NTup
              then do
                mtys' <- share $ ensureTupTypeM mty'
                let es' = map2ML
                      (\e mty' -> makeFrames menv inBang e mty')
                      es
                      mtys'
                return (MECon False (return False) (return NTup) es')
              else do
                menv <- share menv
                env <- menv
                let denv = dataEnv env
                -- Data MyTy a b c = Con1 a b a | Con2 a c
                -- (Con1 1 True [True,False] :: MyTy Int Bool Nat) => (Con1 !1 True [True,False] :: MyTy (BX Int) Bool (BX Nat))
                --   name = "Con1"
                --   ty = MyTy Int Bool Nat
                --   mty' = MyTy (BX Int) Bool (BX Nat)
                case D.lookupTy name denv of
                  Just (TyData1 _ tyVars (_, orig_tys)) -> do
                    -- tyVars = [a,b,c]
                    -- orig_tys = [a,b,a]
                    MTyApp _ _ inst_ts <- mty'
                    -- inst_ts = [(BX Int) Bool (BX Nat)]
                    let sigma = LE.fromList
                          $ map2ML (\a ty -> return (a, ty)) tyVars inst_ts
                    tys' <- share
                      $ foldr
                        (\ty tys' -> cons (substTy sigma ty) tys')
                        nil
                        orig_tys
                    let es' = map2ML
                          (\e ty' -> makeFrames menv inBang e ty')
                          es
                          tys'
                    return (MECon False (return False) (return name) es')
  -- where
  --         --  case es of
  --         --    -- 大変雑な実装 もっとうまくやる方法を知りたい
  --         --    [] -> return (MECon (return False) (return name) nil)
  --         --    _  -> do
  --         --      tyCon <- lookupTyEnv name menv
  --         --      let tyConBody = case tyCon of
  --         --            T.TyForAll _ tyConBody    -> tyConBody
  --         --            T.TyForAllC _ _ tyConBody -> tyConBody
  --         --      let (tys, T.TyApp cname tyVars) =
  --         --            splitLast $ arrowToList tyConBody
  --         --      MTyApp _ sig <- mty'
  --         --      let sigma = substTy (map (\(T.TyVar tyVar) -> tyVar) tyVars) sig
  --         --      let tys' = mapML sigma (convert tys)
  --         --      let es' =
  --         --            map2ML (\e ty' -> makeFrames menv inBang e ty') es tys'
  --         --      return (MECon (return False) (return name) es')
  --   splitLast :: [a] -> ([a], a)
  --   splitLast [x] = ([], x)
  --   splitLast (x:xs) = let (xs', last) = splitLast xs
  --                      in (x:xs', last)
  --   arrowToList :: T.Ty -> [T.Ty]
  --   arrowToList (T.TyForAll _ ty) = arrowToList ty
  --   arrowToList (T.TyForAllC _ _ ty) = arrowToList ty
  --   arrowToList (T.TyArr t1 t2) = let t2' = arrowToList t2
  --                                 in t1:t2'
  --   arrowToList ty = [ty]
makeFrames' menv inBang (Typed (ECase e0 alts) ty) mty' = do
  mty' <- share mty'
  isB <- isBx mty'
  if isB
    then makeFramesEcase menv inBang e0 alts mty'
      `mplus` makeFramesEcaseB menv inBang e0 alts mty'
    else makeFramesEcase menv inBang e0 alts mty'

-- substTy -- TyForAllに非対応
--    :: Monad m => [T.TyVar] -> m (List m (MTy m)) -> m (MTy m) -> m (MTy m)
-- substTy tvs tys = go (makeEnvM tvs tys)
--   where
--     go :: Monad m => m (List m (T.TyVar, m (MTy m))) -> m (MTy m) -> m (MTy m)
--     go menv mty = do
--       ty <- mty
--       case ty of
--         MTyVar x    -> fromMaybeM (return (MTyVar x)) (find x menv)
--         MTyApp t ts -> return (MTyApp t (mapML (go menv) ts))
--     makeEnvM :: Monad m
--              => [T.TyVar]
--              -> m (List m (MTy m))
--              -> m (List m (T.TyVar, m (MTy m)))
--     makeEnvM = map2ML (\v mty -> return (v, mty))
--     find :: Monad m
--          => T.TyVar
--          -> m (List m (T.TyVar, m (MTy m)))
--          -> m (Maybe (m (MTy m)))
--     find key ml = do
--       l <- ml
--       case l of
--         Nil           -> return Nothing
--         Cons mkv rest -> do
--           (k, v) <- mkv
--           if k == key
--             then return (Just v)
--             else find key rest
--     fromMaybeM :: Monad m => m a -> m (Maybe (m a)) -> m a
--     fromMaybeM a mb = do
--       b <- mb
--       Data.Maybe.fromMaybe a b
makeFramesEcase :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
                => m (SnEnv m)
                -> Bool
                -> TExp
                -> [TAlt]
                -> m (MBxTy m)
                -> m (MExp m)
makeFramesEcase menv inBang e0 alts mty' = do
  menv <- share menv
  env <- menv
  t0' <- share $ synthesisB (pend env) (getType e0)
  let e0' = makeFrames menv inBang e0 t0'
  return $ MECase False e0' (makeFramesAlts menv inBang t0' mty' alts)

makeFramesAlts :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
               => m (SnEnv m)
               -> Bool
               -> m (MBxTy m)
               -> m (MBxTy m)
               -> [TAlt]
               -> m (List m (MAlt m))
makeFramesAlts menv inBang mmt0' mExpectedTy alts = do
  menv <- share menv
  env <- menv
  foldr
    (\(pat, g, e) alts' -> do
       let penv = destructP (dataEnv env) pat mmt0'
       env' <- share $ extendAllLocalM (LE.toList penv) menv
       let g' = makeFrames env' inBang g mBool
       let e' = makeFrames env' inBang e mExpectedTy
       cons (return (pat, g', e')) alts')
    nil
    alts

  -- mt0' <- mmt0'
  -- t0' <- convert mt0'
  -- let a = t0' :: BxTy
  -- let result = res
  --       where
  --         {-# NOINLINE res #-}
  --         res = unsafePerformIO
  --           (do
  --              let tc = unifyTAlt t0' alts
  --              tcenv <- convertEnv env
  --              TP.runTC tc tcenv)
  -- case result of
  --   TP.TyError span doc -> mzero -- ここが呼ばれるかは不明
  --   TP.TyOk patEnvs
  --     -> let env_alts = zip patEnvs alts
  --        in foldr
  --             (\(patEnv, (TPat pat _, g, e)) alts' -> do
  --                localenv <- share $ extendAllLocalM (convert patEnv) menv
  --                let g' = makeFrames localenv inBang g mBool
  --                let e' = makeFrames localenv inBang e mExpectedTy
  --                cons (return (patternConvert pat, g', e')) alts')
  --             nil
  --             env_alts
-- unifyTAlt :: BxTy -> [TAlt] -> TP.TC [[(Name, T.Ty)]]
-- unifyTAlt ty alts = do
--   (tpat, altEnvs) <- gatherPatTy alts
--   TP.unify noSrcSpan tpat ty
--   mapM
--     (\env -> mapM
--        (\(n, ty) -> do
--           ty' <- TP.zonkType ty
--           return (n, ty'))
--        env)
--     altEnvs
-- gatherPatTy :: [TAlt] -> TP.TC (T.Ty, [[(Name, T.Ty)]])
-- gatherPatTy [] = do
--   ty <- TP.newMetaTy noSrcSpan
--   return (ty, [])
-- gatherPatTy ((p, g, e):alts) = do
--   (tpat, penv') <- TP.inferP (convertPatL p)
--   (tpat', altEnvs) <- gatherPatTy alts
--   TP.unify noSrcSpan tpat tpat'
--   return (tpat, penv':altEnvs)
makeFramesEcaseB
  :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
  => m (SnEnv m)
  -> Bool
  -> TExp
  -> [TAlt]
  -> m (MBxTy m)
  -> m (MExp m)
makeFramesEcaseB menv inBang e0 alts ty' = do
  tyE0' <- share $ convert $ getType e0
  let e0' = makeFrames menv inBang e0 (mTyB tyE0')
  let ps = map (\(_, _, e) -> makeFramesP 2 e) alts  -- 0,1はs,vの名前と被る
  let isIdenticals = zipWith (all . checkIdenticalMaybe) ps (removeSelf ps)
  let balts = makeFramesBAlts
        (length alts == 1)
        menv
        inBang
        tyE0'
        (zip3 alts ps isIdenticals)
        ty'
  return (MECaseB False e0' balts)
  where
    removeSelf :: [a] -> [[a]]
    removeSelf [] = []
    removeSelf (x:xs) = xs:map (x:) (removeSelf xs)

makeFramesBAlts
  :: (MonadPlus m, Sharing m, MonadFail m, Delay m)
  => Bool
  -> m (SnEnv m)
  -> Bool
  -> m (MBxTy m)
  -> [(TAlt, Maybe (P.Pat, Int), Bool)]
  -> m (MBxTy m)
  -> m (List m (MBAlt m))
makeFramesBAlts _ menv inBang s [] mExpectedTy = nil
makeFramesBAlts
  isLen1
  menv
  inBang
  s
  (((p, g, e), p_e, isIdentical):alts)
  mExpectedTy = do
  menv <- share menv
  env <- menv
  v <- share $ convert (getType e)
  penv <- share $ destructP (dataEnv env) p s
  penv' <- share $ LE.map (\_ ty -> mTyB ty) penv
  let penv_menv = extendAllLocalM (LE.toList penv) menv
  let penv'_menv = extendAllLocalM (LE.toList penv') menv
  let g' = makeFrames penv_menv inBang g mBool
  let e' = makeFrames penv'_menv inBang e mExpectedTy
  if isLen1
    then do
      let exitCond = return $ MEAbs False (return (SName 1)) mTrue
      let reconciler = return
            $ MEAbs False (return (SName 0))
            $ return
            $ MEAbs
              False
              (return (SName 1))
              (return $ MEVar False (return $ SName 0))
      let balt' = return
            ( p
            , g'
            , return
              $ MBranch { mBody = e'
                        , mExitCond = exitCond
                        , mReconciler = reconciler
                        })
      cons balt' (makeFramesBAlts isLen1 menv inBang s alts mExpectedTy)
    else do
      let exitCond = makeFramesExitCond isIdentical menv e p_e v
      let reconciler = makeFramesReconcile p p_e menv s v
      let balt' = return
            ( p
            , g'
            , return
              $ MBranch { mBody = e'
                        , mExitCond = exitCond
                        , mReconciler = reconciler
                        })
      cons balt' (makeFramesBAlts isLen1 menv inBang s alts mExpectedTy)

-- newName :: MonadPlus m => m (SnEnv m) -> m Name
-- newName menv = do
--   env <- menv
--   x   <- liftIO $ getFresh (uniqSupply env)
--   return (SName x)
makeFramesExitCond
  :: (MonadPlus m, Sharing m)
  => Bool
  -> m (SnEnv m)
  -> TExp
  -> Maybe (P.Pat, Int)
  -> m (MBxTy m)
  -> m (MExp m)
makeFramesExitCond isIdentical menv e p_e ty_v = do
  menv <- share menv
  env <- menv
  let v = SName 1
  case p_e of
    Just (p, loc) -> do
      let alt1 = if isIdentical
                 then return (p, mTrue, mTrue)
                 else do
                   env' <- share
                  --   $ addVarToUsed v
                     $ extendAllLocalM
                       (LE.toList $ destructP (dataEnv env) p ty_v)
                       menv
                   b <- checkAnyCanUseComponents env'
                   if b
                     then return
                       ( p
                       , mTrue
                       , return
                         $ MEHole
                           False
                           mBool
                           (setLoc loc (extendLocalM v ty_v env')))
                     else return (p, mTrue, mTrue)
      -- let alt1 = return (p, mTrue, mTrue)
      let alt2 = return (P.PVar NWild, mTrue, mFalse)
      let mcase = return
            $ MECase
              False
              (return (MEVar False (return v)))
              (cons alt1 (cons alt2 nil))
      return $ MEAbs False (return v) mcase
    Nothing       -> return
      $ MEAbs False (return v)
      $ return
      $ MEHole False mBool (setLoc 2 $ extendLocalM v ty_v menv)

checkAnyCanUseComponents :: (MonadPlus m, Sharing m) => m (SnEnv m) -> m Bool
checkAnyCanUseComponents msnenv = do
  snenv <- msnenv
  let env = localEnvM snenv
  LE.any (\f ty -> go ty) env
  where
    go :: (MonadPlus m, Sharing m) => m (MTy m) -> m Bool
    go mty = do
      ty <- mty
      case ty of
        MTyForAll _ _ _ -> return False
        MTyMetaTv _ -> undefined
        _ -> return True

makeFramesP :: Int -> TExp -> Maybe (P.Pat, Int)
makeFramesP loc e = let (ans, i) = go loc e
                    in case ans of
                         (P.PVar _) -> Nothing
                         _          -> Just (ans, i)
  where
    go :: Int -> TExp -> (P.Pat, Int)
    go loc (Typed e ty) = case e of
      ENum i -> (P.PNum i, loc)
      EChar c -> (P.PChar c, loc)
      -- ECon False NTup es -> let (es', i) = foldr
      --                             (\e (l, i) -> let (e', i') = go i e
      --                                           in (e':l, i'))
      --                             ([], loc)
      --                             es
      --                       in (P.PCon NTup es', i)
      ECon False name es -> let (es', i) = foldl
                                  (\(l, i) e -> let (e', i') = go i e
                                                in (e':l, i'))
                                  ([], loc)
                                  es
                            in (P.PCon name (reverse es'), i)
      ECase e0 [(p, g, e)] -> go loc e -- caseが一つなら飛ばして考える（letと同じ）
      _ -> (P.PVar $ SName loc, loc + 1)

addVarToUsed :: Monad m => Name -> m (SnEnv m) -> m (SnEnv m)
addVarToUsed name menv = do
  env <- menv
  return $ env { usedNames = name:usedNames env }

setLoc :: Monad m => Int -> m (SnEnv m) -> m (SnEnv m)
setLoc i menv = do
  env <- menv
  return $ env { loc_ = i }

makeFramesReconcile
  :: (MonadPlus m, Sharing m)
  => P.Pat
  -> Maybe (P.Pat, Int)
  -> m (SnEnv m)
  -> m (MBxTy m)
  -> m (MBxTy m)
  -> m (MExp m)
makeFramesReconcile p0 p_maybe menv ty_s ty_v = case checkJustConst p0 of
  Just e  -> do
    let s = SName 0
    let v = SName 1
    return $ MEAbs False (return s) $ return $ MEAbs False (return v) e
  Nothing -> do
    menv <- share menv
    env <- menv
    let s = SName 0
    let v = SName 1
    case p_maybe of
      Just (p, loc) -> do
        env' <- share
          $ addVarToUsed v
          $ extendLocalM
            s
            ty_s
            (extendLocalM
               v
               ty_v
               (extendAllLocalM
                  (LE.toList $ destructP (dataEnv env) p ty_v)
                  menv))
        let alt1 =
              if frame_default env
              then return
                (p, mTrue, return (MEHole False ty_s (setLoc loc env')))
                <|> return
                  (p, mTrue, return (MEHoleUP False p0 ty_s (setLoc loc env')))
              else return
                (p, mTrue, return (MEHole False ty_s (setLoc loc env')))
        let mcase = return
              $ MECase False (return (MEVar False (return v))) (cons alt1 nil)
        return $ MEAbs False (return s) $ return $ MEAbs False (return v) mcase
      Nothing       -> do
        env' <- share (extendLocalM s ty_s (extendLocalM v ty_v menv))
        let e' = if frame_default env
                 then if checkJustVar p0
                      then return $ MEHoleUP False p0 ty_s (setLoc 2 env')
                      else return (MEHoleApp False ty_s (setLoc 2 env'))
                        <|> return (MEHoleUP False p0 ty_s (setLoc 2 env'))
                 else return (MEHole False ty_s (setLoc 2 env'))
        return $ MEAbs False (return s) $ return $ MEAbs False (return v) e'
  where
    checkJustConst :: Monad m => P.Pat -> Maybe (m (MExp m))
    checkJustConst p = case p of
      P.PNum i      -> Just (return $ MENum False (return i))
      P.PChar c     -> Just (return $ MEChar False (return c))
      P.PCon name l -> case go l of
        Nothing -> Nothing
        Just l' -> do
          let l'' = foldr cons nil l'
          Just $ return $ MECon False (return False) (return name) l''
      P.PVar _      -> Nothing
      where
        go :: Monad m => [P.Pat] -> Maybe [m (MExp m)]
        go [] = return []
        go (p:ps) = do
          ps' <- go ps
          p' <- checkJustConst p
          return (p':ps')

    checkJustVar :: P.Pat -> Bool
    checkJustVar p = case p of
      P.PVar _ -> True
      _        -> False

checkIdentical :: P.Pat -> P.Pat -> Bool
checkIdentical (P.PVar x) _ = False
checkIdentical _ (P.PVar x) = False
checkIdentical (P.PNum i) (P.PNum j) = i /= j
checkIdentical (P.PChar c) (P.PChar c') = c /= c'
checkIdentical (P.PCon name1 ps1) (P.PCon name2 ps2) = name1 /= name2
  || any (uncurry checkIdentical) (zip ps1 ps2)
checkIdentical _ _ = True

checkIdenticalMaybe :: Maybe (P.Pat, Int) -> Maybe (P.Pat, Int) -> Bool
checkIdenticalMaybe (Just (p1, _)) (Just (p2, _)) = checkIdentical p1 p2
checkIdenticalMaybe _ _ = False

-- -- MECase (m (MExp m)) (m (List m (MAlt m)))
-- patternConvert :: Pat -> MPat
-- patternConvert (PNum i) = P.PNum i
-- patternConvert (PChar c) = P.PChar c
-- patternConvert (PVar v) = P.PVar v
-- patternConvert (PCon name l) = P.PCon name (map patternConvert l)
-- mtyはshare済みと仮定
-- destructPBX
--   :: (MonadPlus m, Sharing m) => DataEnv -> P.Pat -> m (MTy m) -> m (MTyEnv m)
-- destructPBX denv p ty = LE.map (\_ ty -> mTyB ty) $ destructP denv p ty
destructPMaybe :: (MonadPlus m, Sharing m)
               => DataEnv
               -> P.Pat
               -> m (MTy m)
               -> Maybe (m (MTyEnv m))
destructPMaybe denv (P.PVar x) ty = Nothing
destructPMaybe denv p ty = Just $ destructP denv p ty

-- mtyはshare済みと仮定
destructP
  :: (MonadPlus m, Sharing m) => DataEnv -> P.Pat -> m (MTy m) -> m (MTyEnv m)
destructP denv (P.PVar x) ty = LE.singleton x ty
destructP denv (P.PNum i) ty = LE.empty
destructP denv (P.PChar c) ty = LE.empty
destructP denv (P.PCon cname ps) mty      -- ps = [x, y, z]
  = do
    ty <- mty
    let MTyApp _ tname inst_ts = ty -- inst_ts = [Int, Bool, Nat]
    if tname == TName "(,..,)"
      then foldrML (\env1 env -> LE.insertAll env1 env) LE.empty
        $ map2ML (\p ty -> destructP denv p ty) ps inst_ts
      else case D.lookup tname denv of
        Just (D.TyData _ tyvars nametys)        -- tyvars = a b c of
          -> do
            let Just tys = Prelude.lookup cname nametys -- tys = [a,b,a]
            let sigma = LE.fromList
                  $ map2ML (\a ty -> return (a, ty)) tyvars inst_ts
            tys' <- share
              $ foldr (\ty tys' -> cons (substTy sigma ty) tys') nil tys
            let tmp = map2ML (\p ty' -> destructP denv p ty') ps tys'
            foldrML (\env1 env -> LE.insertAll env1 env) LE.empty tmp
        Nothing -> mzero

-- mtyはshare済みと仮定
-- destructPR :: (MonadPlus m, Sharing m)
--            => m (SnEnv m)
--            -> DataEnv
--            -> P.Pat
--            -> m (MTy m)
--            -> m (MExp m)
-- destructPR env denv (P.PVar x) ty = return $ MEHole False ty env
-- destructPR env denv (P.PNum i) ty = return $ MENum False (return i)
-- destructPR env denv (P.PChar c) ty = return $ MEChar False (return c)
-- destructPR env denv (P.PCon cname ps) mty      -- ps = [x, y, z]
--   = do
--     ty <- mty
--     let MTyApp _ tname inst_ts = ty -- inst_ts = [Int, Bool, Nat]
--     if tname == TName "(,..,)"
--       then return
--         $ MECon False (return False) (return $ CName "(,..,)")
--         $ map2ML (destructPR env denv) ps inst_ts
--       else case D.lookup tname denv of
--         Just (D.TyData _ tyvars nametys)        -- tyvars = a b c of
--           -> do
--             let Just tys = Prelude.lookup cname nametys -- tys = [a,b,a]
--             let sigma = LE.fromList
--                   $ map2ML (\a ty -> return (a, ty)) tyvars inst_ts
--             tys' <- share
--               $ foldr (\ty tys' -> cons (substTy sigma ty) tys') nil tys
--             let es' = map2ML (destructPR env denv) ps tys'
--             return $ MECon False (return False) (return cname) es'
--         Nothing -> mzero
substTy :: Monad m => m (LE.Env m T.TyVar (MTy m)) -> T.Ty -> m (MTy m)
substTy sigma (T.TyApp tname tys) =
  let tys' = foldr (\ty tys' -> cons (substTy sigma ty) tys') nil tys
  in return $ MTyApp False tname tys'
substTy sigma (T.TyVar a) = do
  look <- LE.lookup a sigma
  case look of
    Just ty -> ty
-- Data MyTy a b c = Con1 a b a | Con2 a c
--  case (e :: (MyTy Int Bool Nat)) of
--     Con1 x y z -> ...
-- case (e :: (Int, Bool,Nat)) of
--    (x, y, z) ->
