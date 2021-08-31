{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -fwarn-missing-signatures #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- module Typing (
--     defaultTyEnv, defaultSynonyms, toTyEnv, TyEnv(..), Synonyms(..),
--     inferExp, checkExp, inferDecls, inferDeclToTExp
--   ) where
module Typing where

import           EnvLike as E
import           Err
import           Name
import           SrcLoc
import           Syntax as S
import           Util
import           Control.Monad.Except
import           Control.Monad.State (StateT(..), evalStateT)
import qualified Control.Monad.State (get, put)
import           Control.Monad.Trans.Writer (runWriterT)
import           Control.Monad.Writer (WriterT, censor, listen, tell)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import qualified Data.Set as S
import           Text.PrettyPrint as T hiding ((<>))
import           Text.PrettyPrint.HughesPJClass as T hiding ((<>))
import qualified Data.Graph as G
import           Data.List (intercalate, nub, union, (\\))
import           Control.Monad.Reader
import           Data.IORef
import           Data.Maybe
import           Debug.Trace

putStrD :: String -> IO ()

#ifdef DEBUG
putStrD = putStrLn

#else
putStrD = const (return ())
#endif

defaultTyEnv :: TyEnv
defaultTyEnv = E.fromList
  [ (CName "True", TyBool)
  , (CName "False", TyBool)
  , (CName "None", TyNone)
  , (CName "Left", TyForAll [a, b] (TyVar a --> TyEither (TyVar a) (TyVar b)))
  , (CName "Right", TyForAll [a, b] (TyVar b --> TyEither (TyVar a) (TyVar b)))
  , (CName "Nothing", TyForAll [a] (TyMaybe (TyVar a)))
  , (CName "Just", TyForAll [a] (TyVar a --> TyMaybe (TyVar a)))
  , (NCons, TyForAll [a] (TyVar a --> TyList (TyVar a) --> TyList (TyVar a)))
  , (NNil, TyForAll [a] (TyList (TyVar a)))
    -- (Name "checkEq", TyS [a]
    --                  (TyB (TyVar a)
    --                   -->
    --                   TyB (TyVar a)
    --                   -->
    --                   TyB (TyEither (TyTup [TyVar a, TyVar a]) (TyVar a)))),
  , (Name "showInt", TyInt --> TyList TyChar)
  , ( Name "comp"
    , TyForAll
        [a, b, c]
        (TyArr (TyVar b) (TyVar c)
         --> TyArr (TyVar a) (TyVar b)
         --> TyArr (TyVar a) (TyVar c)))
  , (Name "orElse", TyForAll [] (TyBool --> TyBool --> TyBool))
  , (Name "inspect", TyForAll [a] (TyB (TyVar a) --> TyB (TyVar a)))]
  where
    a = BoundTv (Name "a")

    b = BoundTv (Name "b")

    c = BoundTv (Name "c")

defaultSynonyms :: Synonyms
defaultSynonyms = E.fromList [(TName "String", ([], TyList TyChar))]

newtype Synonyms = S (M.Map TName ([TyVar], Ty))
  deriving (EnvLike TName ([TyVar], Ty))

newtype TyEnv = E (M.Map Name Ty)
  deriving (EnvLike Name Ty)

instance Show Synonyms where
  show = showEnvLike

instance Show TyEnv where
  show = render . pprTyEnv

pprTyEnv :: TyEnv -> Doc
pprTyEnv env = vcat
  $ map (\(k, v) -> hsep [text (showKey k), text "::", pPrint v]) kvs
  where
    kvs = E.toList env

    maxLen = foldr (max . length . show . fst) 0 kvs

    showKey k = take maxLen (show k ++ repeat ' ')

showTyEnv :: TyEnv -> String
showTyEnv env = go $ E.toList env
  where
    go [] = ""
    go [(k, v)] = show k ++ " :: " ++ show v
    go ((k, v):rest) = show k ++ " :: " ++ show v ++ ", " ++ go rest

emap :: (Ty -> Ty) -> TyEnv -> TyEnv
emap f (E m) = E $ fmap f m

toTyEnv :: (TyEnv, Synonyms) -> [TyDecl] -> (TyEnv, Synonyms)
toTyEnv (te, syn) [] = (te, syn)
toTyEnv (te, syn) (TyData n args cdefs:decls) =
  let (te', syn') = toTyEnv (te, syn) decls
  in ( foldr
         (\(k, rs) -> let eargs = nub (concatMap freeTyVars rs) \\ args
                          ty = TyForAllC args eargs
                            $ foldr TyArr (TyApp n (map TyVar args)) rs
                      in insert k ty)
         te'
         cdefs
     , syn')
toTyEnv (te, syn) (TyType tn ns ty:decls) =
  let (te', syn') = toTyEnv (te, syn) decls
  in (te', insert tn (ns, ty) syn')

type UniqSupply = IORef Int

data TcEnv = TcEnv { tcUniqRef :: UniqSupply
                   , tcTyEnv :: TyEnv
                   , tcBxTyEnv :: TyEnv
                   , tcSynonyms :: Synonyms
                   }

newtype TC a = TC { runTC :: TcEnv -> IO (TCResult a) }

data TCResult a = TyOk a
                | TyError SrcSpan Doc

instance Monad TC where
  return x = TC $ \_ -> return (TyOk x)

  TC m >>= f = TC
    $ \env -> do
      x <- m env
      case x of
        TyError span msg -> return $ TyError span msg
        TyOk res         -> runTC (f res) env

instance MonadReader TcEnv TC where
  ask = TC $ \env -> return (TyOk env)

  local f m = TC $ \env -> runTC m (f env)

instance Functor TC where
  fmap = liftM

instance Applicative TC where
  pure = return

  (<*>) = ap

tyError' :: Doc -> TC a
tyError' = tyError noSrcSpan

tyError :: SrcSpan -> Doc -> TC a
tyError span msg = TC $ \_ -> return (TyError span msg)

instance MonadIO TC where
  liftIO m = TC $ \_ -> fmap TyOk m

newTcRef :: a -> TC (IORef a)
newTcRef v = liftIO $ newIORef v

readTcRef :: IORef a -> TC a
readTcRef v = liftIO $ readIORef v

writeTcRef :: IORef a -> a -> TC ()
writeTcRef ref v = liftIO $ writeIORef ref v

tyEnvLocal :: TyEnv -> TC a -> TC a
tyEnvLocal tenv = local replaceEnv
  where
    replaceEnv env = env { tcTyEnv = tenv }

extendLocal :: Name -> Ty -> TC a -> TC a
extendLocal x t = local extend
  where
    extend env = env { tcTyEnv = insert x t (tcTyEnv env)
                     , tcBxTyEnv = delete x (tcBxTyEnv env)
                     }

extendAllLocal :: [(Name, Ty)] -> TC a -> TC a
extendAllLocal [] k = k
extendAllLocal ((x, t):binds) k = extendLocal x t (extendAllLocal binds k)

extendBxAllLocal :: [(Name, Ty)] -> TC a -> TC a
extendBxAllLocal [] k = k
extendBxAllLocal ((x, t):binds) k =
  extendBxLocal x t (extendBxAllLocal binds k)

extendBxLocal :: Name -> Ty -> TC a -> TC a
extendBxLocal x t = local extend
  where
    extend env = env { tcBxTyEnv = insert x t (tcBxTyEnv env)
                     , tcTyEnv = delete x (tcTyEnv env)
                     }

clearBXLocal :: TC a -> TC a
clearBXLocal = local clearBxEnv
  where
    clearBxEnv env = env { tcBxTyEnv = E.empty }

resolveSyn :: Ty -> TC Ty
resolveSyn ty = do
  syn <- asks tcSynonyms
  replaceSynonyms syn ty

-- TC Monad is used because it may throw an error
replaceSynonyms :: Synonyms -> Ty -> TC Ty
replaceSynonyms syn (TyVar x) = return $ TyVar x
replaceSynonyms
  syn
  (TyMetaV x) = return $ TyMetaV x -- it only replace synonyms shallowly
replaceSynonyms syn (TyForAll ns t) = TyForAll ns <$> replaceSynonyms syn t
replaceSynonyms syn (TyForAllC ns ms t) =
  TyForAllC ns ms <$> replaceSynonyms syn t
replaceSynonyms syn (TyApp tname ts) = case E.lookup tname syn of
  Nothing -> TyApp tname <$> mapM (replaceSynonyms syn) ts
  Just (ps, t)
    | length ps == length ts -> TySyn (TyApp tname ts)
      <$> replaceSynonyms syn (substTy ps ts t)
  _ -> tyError noSrcSpan
    $ hsep
      [ text "Type synonym"
      , quotes (pPrint tname)
      , text "must be fully-applied"]
replaceSynonyms syn (TySyn origTy ty) = TySyn origTy <$> replaceSynonyms syn ty

newUnique :: TC Int
newUnique = do
  ref <- asks tcUniqRef
  i <- readTcRef ref
  let i' = i + 1
  i' `seq` writeTcRef ref i'
  return i'

newMetaTv :: SrcSpan -> TC MetaTv
newMetaTv span = do
  u <- newUnique
  ref <- newTcRef Nothing
  return $ MetaTv u span ref

newMetaTy :: SrcSpan -> TC Ty
newMetaTy = fmap TyMetaV . newMetaTv

zonkType :: Ty -> TC Ty
zonkType (TyVar n) = return $ TyVar n
zonkType (TyApp t ts) = TyApp t <$> (mapM zonkType ts)
zonkType (TyForAll vs t) = TyForAll vs <$> zonkType t
zonkType (TyForAllC vs evs t) = TyForAllC vs evs <$> zonkType t
zonkType (TyMetaV m) = do
  mty <- readTv m
  case mty of
    Nothing -> return (TyMetaV m)
    Just ty -> do
      ty' <- zonkType ty
      writeTv m ty'
      return ty'
zonkType (TySyn origTy ty) = do
  origTy' <- zonkType origTy
  ty' <- zonkType ty
  return $ TySyn origTy' ty'

lookupVar :: SrcSpan -> Name -> TC PolyTy
lookupVar span x = do
  tenv <- asks tcTyEnv
  case E.lookup x tenv of
    Nothing -> do
      benv <- asks tcBxTyEnv
      case E.lookup x benv of
        Nothing -> tyError span
          $ hsep [text "Undefined variable:", pPrint x]
          $$ sep
            [ text "Environment searched:"
            , nest 2 (pprTyEnv tenv $$ pprTyEnv benv)]
        Just ty -> return $ TyB ty
    Just ty -> return ty

instPoly :: SrcSpan -> PolyTy -> BodyTy -> TC ()
instPoly span polyty expected = do
  t <- instantiate span polyty
  unify span t expected

instantiateP :: SrcSpan -> PolyTy -> TC MonoTy
instantiateP span (TyForAllC ts ets t) = do
  mvs <- mapM (const $ newMetaTy span) ts
  svs <- mapM (fmap TyVar . newSkolemTyVar) ets
  return $ substituteTyVar (zip ets svs) $ substituteTyVar (zip ts mvs) t
instantiateP span t = instantiate span t

instantiate :: SrcSpan -> PolyTy -> TC MonoTy
instantiate span (TyForAll ts t) = do
  mvs <- mapM (const $ newMetaTy span) ts
  return $ substituteTyVar (zip ts mvs) t
instantiate span (TyForAllC ts ets t) = do
  mvs1 <- mapM (const $ newMetaTy span) ts
  mvs2 <- mapM (const $ newMetaTy span) ets
  return $ substituteTyVar (zip ets mvs2) $ substituteTyVar (zip ts mvs1) t
instantiate span t = return t

substituteTyVar :: [(TyVar, MonoTy)] -> BodyTy -> BodyTy
substituteTyVar [] t = t
substituteTyVar table (TyVar t) = fromMaybe (TyVar t) $ Prelude.lookup t table
substituteTyVar table (TyApp tn ts) = TyApp tn $ map (substituteTyVar table) ts
substituteTyVar table (TyMetaV v) = TyMetaV v
substituteTyVar table (TyForAll ts t) =
  let table' = filter (not . (`elem` ts) . fst) table
  in TyForAll ts (substituteTyVar table' t)
substituteTyVar table (TyForAllC vs evs t) =
  let table' = filter (not . (`elem` vs) . fst)
        $ filter (not . (`elem` evs) . fst) table
  in TyForAllC vs evs (substituteTyVar table' t)
substituteTyVar table (TySyn oty ty) =
  TySyn (substituteTyVar table oty) (substituteTyVar table ty)

inferBodyTy :: LExp -> TC BodyTy
inferBodyTy le = do
  ty <- newMetaTy (getLoc le)
  checkBodyTy le ty
  return ty

inferPolyTy :: LExp -> TC PolyTy
inferPolyTy e = do
  expTy <- inferBodyTy e
  envTyps <- getEnvTypes
  envTvs <- getMetaTyVars envTyps
  expTvs <- getMetaTyVars [expTy]
  let forallTvs = expTvs \\ envTvs
  quantify forallTvs expTy

getEnvTypes :: TC [PolyTy]
getEnvTypes = do
  tenv <- asks tcTyEnv
  benv <- asks tcBxTyEnv
  return $ E.values tenv ++ E.values benv

getMetaTyVars :: [Ty] -> TC [MetaTv]
getMetaTyVars ts = metaTyVars <$> mapM zonkType ts

quantify :: [MetaTv] -> BodyTy -> TC PolyTy
quantify tvs ty = do
  mapM_ bind (tvs `zip` newBinders)
  ty' <- zonkType ty
  return (TyForAll newBinders ty')
  where
    usedBinders = tyVarBinders ty -- always empty?

    newBinders = take (length tvs) (allFancyBinders \\ usedBinders)

    bind (metav, typev) = writeTv metav (TyVar typev)

readTv :: MetaTv -> TC (Maybe MonoTy)
readTv (MetaTv _ _ ref) = readTcRef ref

writeTv :: MetaTv -> MonoTy -> TC ()
writeTv (MetaTv _ _ ref) ty = writeTcRef ref (Just ty)

allFancyBinders :: [TyVar]
allFancyBinders = map (BoundTv . Name)
  $ [[x] | x <- ['a' .. 'z']]
  ++ [x:show i | i <- [1 :: Integer ..], x <- ['a' .. 'z']]

unify :: SrcSpan -> MonoTy -> MonoTy -> TC ()
unify span ty1 ty2 = do
  ty1' <- resolveSyn ty1
  ty2' <- resolveSyn ty2
  -- liftIO $ putStrLn $ "Start unifying " ++ show ty1' ++ " and " ++ show ty2' ++ " at " ++ show span
  unifyWork span ty1' ty2'

unifyWork :: SrcSpan -> MonoTy -> MonoTy -> TC ()
unifyWork span (TySyn _ t1) t2 = unifyWork span t1 t2
unifyWork span t1 (TySyn _ t2) = unifyWork span t1 t2
unifyWork span (TyVar x1) (TyVar x2)
  | x1 == x2 = return ()
unifyWork span (TyMetaV m1) (TyMetaV m2)
  | m1 == m2 = return ()
unifyWork span (TyMetaV m) ty = unifyVar span False m ty
unifyWork span tx (TyMetaV m) = unifyVar span True m tx
unifyWork span (TyArr s1 t1) (TyArr s2 t2) =
  unifyWork span s2 s1 >> unifyWork span t1 t2
unifyWork span (TyApp n1 ts1) (TyApp n2 ts2)
  | n1 == n2 && length ts1 == length ts2 = zipWithM_ (unifyWork span) ts1 ts2
unifyWork span ty1 ty2 = do
  ty1' <- zonkType ty1
  ty2' <- zonkType ty2
  tyError span $ docMatchFailure ty1' ty2'

unifyVar :: SrcSpan -> Bool -> MetaTv -> MonoTy -> TC ()
unifyVar span isFlipped m ty = do
  --  liftIO $ putStrLn $ "Unify var " ++ show m ++ " against " ++ show ty
  r <- readTv m
  case r of
    Just ty' -> if isFlipped
                then unify span ty' ty
                else unify span ty ty'
    Nothing  -> unifyUnboundVar span m ty

unifyUnboundVar :: SrcSpan -> MetaTv -> MonoTy -> TC ()
unifyUnboundVar span m1 ty@(TyMetaV m2) = do
  r <- readTv m2
  case r of
    Just ty' -> unify span (TyMetaV m1) ty'
    Nothing  -> writeTv m1 ty
unifyUnboundVar span m ty = do
  ty' <- zonkType ty
  ms <- getMetaTyVars [ty']
  if m `elem` ms
    then tyError span
      $ text "Occurrence check failed for"
      <+> quotes (pPrint m)
      <+> text "in"
      <+> pPrint ty'
    else writeTv m ty

checkBodyTy :: LExp -> BodyTy -> TC ()
checkBodyTy (L span e) expectedTy = do
  -- liftIO $ putStrD $ "Checking " ++ show e ++ " against " ++ show expectedTy
  go e
  where
    go :: S.Exp -> TC ()
    go (S.EVar x) = do
      tx <- lookupVar span x
      instPoly span tx expectedTy
    go (S.EAbs x e) = do
      (argTy, resTy) <- ensureFunType span expectedTy
      extendLocal x argTy $ checkBodyTy e resTy
    go (S.EApp (L span' (S.EAbs x e2)) e1) = do
      e1Ty <- inferPolyTy e1
      extendLocal x e1Ty $ checkBodyTy e2 expectedTy
    go (S.EApp e1 e2) = do
      funTy <- inferBodyTy e1
      (argTy, resTy) <- ensureFunType span funTy
      checkBodyTy e2 argTy
      unify span resTy expectedTy
    go (S.EAdd e1 e2) = do
      ensureBaseType span TyInt expectedTy
      checkBodyTy e1 TyInt
      checkBodyTy e2 TyInt
    go (S.EEq e1 e2) = do
      ensureBaseType span TyBool expectedTy
      ty <- newMetaTy span
      checkBodyTy e1 ty
      checkBodyTy e2 ty
    go (S.ELess e1 e2) = do
      ensureBaseType span TyBool expectedTy
      checkBodyTy e1 TyInt
      checkBodyTy e2 TyInt
    go (S.ENeg e) = do
      ensureBaseType span TyInt expectedTy
      checkBodyTy e TyInt
    go (S.ENum _) = ensureBaseType span TyInt expectedTy
    go (S.EChar e) = ensureBaseType span TyChar expectedTy
    go (S.ELift e1 e2) = do
      (argTy, resTy) <- ensureFunType span expectedTy
      argTy' <- ensureBxType span argTy
      resTy' <- ensureBxType span resTy
      checkBodyTy e1 (argTy' --> resTy')
      checkBodyTy e2 (argTy' --> resTy' --> argTy')
    go (S.EAbort e) = checkBodyTy e (TyList TyChar)
    go (S.ECon b NTup es) = do
      expectedTy' <- if b
                     then ensureBxType span expectedTy
                     else return expectedTy
      ts <- ensureTupType span (length es) expectedTy'
      zipWithM_
        (\e t -> checkBodyTy
           e
           (if b
            then TyB t
            else t))
        es
        ts
    go (S.ECon b cname es) = do
      conTy <- instantiate span =<< lookupVar span cname
      ty <- convertTy b conTy
      retTy <- foldM app ty es
      unify span retTy expectedTy
      where
        -- convertTy converts a -> b -> c to BX a -> BX b -> BX c for example
        convertTy False t = return t
        convertTy True (TyArr t1 t2) =
          liftM2 (-->) (convertArg t1) (convertTy True t2)
        convertTy True ty = return $ TyB ty

        convertArg t = return $ TyB t

        app ty e = do
          (argTy, resTy) <- ensureFunType span ty
          checkBodyTy e argTy
          return resTy
    go (S.ECase e0 alts) = do
      tpat <- checkAlts alts expectedTy
      checkBodyTy e0 tpat
    go (S.ECaseB e0 alts) = do
      expectedTyUnB <- ensureBxType span expectedTy
      tpat <- checkBAlts alts expectedTyUnB
      checkBodyTy e0 (TyB tpat)
    go (S.EConstL e) = do
      ty <- ensureBxType span expectedTy
      checkBodyTy e ty

checkAlts :: [(LPat, LGuard, LExp)] -> MonoTy -> TC MonoTy
checkAlts [] expectedTy = newMetaTy noSrcSpan
checkAlts ((p, g, e):alts) expectedTy = do
  (tpat, env) <- inferP p
  extendAllLocal env $ checkBodyTy g TyBool
  extendAllLocal env $ checkBodyTy e expectedTy
  tpat' <- checkAlts alts expectedTy
  unify (getLoc p) tpat tpat'
  return tpat

checkBAlts :: [(LPat, LGuard, Branch)] -> MonoTy -> TC MonoTy
checkBAlts [] expectedTyUnB = newMetaTy noSrcSpan
checkBAlts ((p, g, Branch e cond reconcile):alts) expectedTyUnB = do
  (tpat, env) <- inferP p
  extendAllLocal env $ checkBodyTy g TyBool
  checkBodyTy cond (expectedTyUnB --> TyBool)
  checkBodyTy reconcile (tpat --> expectedTyUnB --> tpat)
  extendBxAllLocal env $ checkBodyTy e (TyB expectedTyUnB)
  tpat' <- checkBAlts alts expectedTyUnB
  unify (getLoc p) tpat tpat'
  return tpat

inferP :: LPat -> TC (MonoTy, [(Name, MonoTy)])
inferP (L _ (S.PNum _)) = return (TyInt, [])
inferP (L _ (S.PChar _)) = return (TyChar, [])
inferP (L s (S.PVar NWild)) = do
  ty <- newMetaTy s
  return (ty, [])
inferP (L s (S.PVar x)) = do
  ty <- newMetaTy s
  return (ty, [(x, ty)])
inferP (L s (S.PCon NTup ps)) = do
  results <- mapM inferP ps
  let env = concatMap snd results
  let typ = TyTup $ map fst results
  return (typ, env)
inferP (L s (S.PCon c ps)) = do
  conTy <- instantiateP s
    =<< lookupVar s c  {- FIXME: This is problematic for existential types. -}
  -- liftIO $ putStrD $ (show c) ++ " :: " ++ show conTy
  (tret, env) <- foldM app (conTy, []) ps
  case tret of
    TyArr _ _ -> tyError s
      $ hsep [text "Constructor", pPrint c, text "must be fully applied."]
    _         -> return (tret, env)
  where
    app (ty, env) p = do
      (argTy, retTy) <- ensureFunType s ty
      (pTy, penv) <- inferP p
      unify s pTy argTy
      return (retTy, penv ++ env)

docMatchFailure :: MonoTy -> MonoTy -> Doc
docMatchFailure inferred expected = vcat
  [ hsep [text "Expected:", pPrint expected]
  , hsep [text "Inferred:", pPrint inferred]]

ensureBaseType :: SrcSpan -> MonoTy -> MonoTy -> TC ()
ensureBaseType span tb ty
  | tb == ty = return ()
ensureBaseType span tb ty = unify span tb ty

ensureFunType :: SrcSpan -> MonoTy -> TC (MonoTy, MonoTy)
ensureFunType span (TyArr t1 t2) = return (t1, t2)
ensureFunType span ty = do
  t1 <- newMetaTy span
  t2 <- newMetaTy span
  unify span (t1 --> t2) ty
  return (t1, t2)

ensureBxType :: SrcSpan -> MonoTy -> TC MonoTy
ensureBxType span (TyB t) = return t
ensureBxType span ty = do
  t <- newMetaTy span
  unify span (TyB t) ty
  return t

ensureTupType :: SrcSpan -> Int -> MonoTy -> TC [MonoTy]
ensureTupType span n (TyTup ts)
  | length ts == n = return ts
ensureTupType span n ty = do
  ts <- replicateM n (newMetaTy span)
  unify span (TyTup ts) ty
  return ts

inferExp :: LExp -> (TyEnv, Synonyms) -> IO (Err PolyTy)
inferExp e (env, syn) = do
  ref <- newIORef 1
  convertResult
    <$> runTC
      (zonkType =<< inferPolyTy e)
      TcEnv { tcTyEnv = env
            , tcBxTyEnv = E.empty
            , tcUniqRef = ref
            , tcSynonyms = syn
            }

checkTypeUnifiable :: TyEnv -> Synonyms -> PolyTy -> PolyTy -> IO Bool
checkTypeUnifiable env syn ty1 ty2 = do
  ref <- newIORef 1
  tc <- runTC
    (go ty1 ty2)
    TcEnv { tcTyEnv = env
          , tcBxTyEnv = E.empty
          , tcUniqRef = ref
          , tcSynonyms = syn
          }
  case convertResult tc of
    Bad s -> return False
    Ok _  -> return True
  where
    go ty1 ty2 = do
      ty1' <- instantiate noSrcSpan ty1
      ty2' <- instantiate noSrcSpan ty2
      unify noSrcSpan ty1' ty2'
      return ()

checkExp :: LExp -> (TyEnv, Synonyms) -> PolyTy -> IO (Err ())
checkExp e (env, sym) ty = do
  ref <- newIORef 1
  let conf = TcEnv { tcTyEnv = env
                   , tcBxTyEnv = E.empty
                   , tcUniqRef = ref
                   , tcSynonyms = sym
                   }
  fmap convertResult
    $ flip runTC conf
    $ do
      ty' <- instantiate (getLoc e) ty
      checkBodyTy e ty'

convertResult :: TCResult a -> Err a
convertResult (TyOk a) = Ok a
convertResult (TyError i s) = Bad
  (render $ vcat [hsep [text "At", text (show i)], nest 4 s])

inferDecls :: [LDecl] -> (TyEnv, Synonyms) -> IO (Err TyEnv)
inferDecls decls (env, syn) = do
  ref <- newIORef 1
  let declss = map unSCC (G.stronglyConnComp graph)
  let conf = TcEnv { tcTyEnv = env
                   , tcBxTyEnv = E.empty
                   , tcUniqRef = ref
                   , tcSynonyms = syn
                   }
  fmap convertResult
    $ flip runTC conf
    $ foldM (flip simpleTypeInfer) env declss
  where
    unSCC (G.AcyclicSCC x) = [x]
    unSCC (G.CyclicSCC xs) = xs

    graph = [(L i (Decl n t e), n, freeVars e) | L i (Decl n t e) <- decls]

simpleTypeInfer :: [LDecl] -> TyEnv -> TC TyEnv
simpleTypeInfer decls env = tyEnvLocal env
  $ do
    let ns = [n | Decl n _ _ <- map unLoc decls]
    ms <- mapM (\(L s (Decl _ t _)) -> maybe (newMetaTy s) return t) decls
    -- typing as if fix (\(f1,f2,..,fn) -> (e1,e2,...,en))
    tys <- extendAllLocal (zip ns ms)
      $ zipWithM
        (\(L span (Decl n t e)) m -> do
           ty <- inferBodyTy e
           -- We defer the check if a declaration has a signature.
           when (isNothing t) (unify span ty m)
           return ty)
        decls
        ms
    -- generalize obtained result
    envTyps <- getEnvTypes
    envTvs <- getMetaTyVars envTyps
    tys' <- zipWithM
      (\t (L span (Decl _ ann _)) -> do
         expTvs <- getMetaTyVars [t]
         pty <- quantify (expTvs \\ envTvs) t
         tt <- zonkType t
         -- liftIO $ putStrD ("Before gen: " ++ show tt)
         -- liftIO $ putStrD ("Env ty vars: " ++ show envTvs)
         -- liftIO $ putStrD ("Exp ty vars: " ++ show expTvs)
         case ann of
           Nothing -> return pty
           Just t' -> do
             -- liftIO $ putStrD ("Checking " ++ show pty ++ " conforms " ++ show t')
             subsCheck span pty t' >> return t')
      tys
      decls
    ts <- mapM zonkType tys'
    return $ insertAll (zip ns ts) env

subsCheck :: SrcSpan -> PolyTy -> PolyTy -> TC ()
subsCheck span sigma1 sigma2@(TyForAll _ _) = do
  (skolTvs, ty2) <- skolemize sigma2
  subsCheck span sigma1 ty2
  escTvs <- getFreeTyVars [sigma1]
  let badTvs = filter (`elem` escTvs) skolTvs
  unless (null badTvs)
    $ tyError span
    $ sep
      [ text "The inferred type:"
      , nest 4 $ quotes (pPrint sigma1)
      , text "is not polymorphic enough for the annotation:"
      , nest 4 $ quotes (pPrint sigma2)]
subsCheck span sigma1@(TyForAll _ _) ty2 = do
  ty1 <- instantiate span sigma1
  subsCheck span ty1 ty2
subsCheck span ty1 ty2 = unify span ty1 ty2

skolemize :: PolyTy -> TC ([TyVar], BodyTy)
skolemize (TyForAll tvs ty) = do
  sks <- mapM newSkolemTyVar tvs
  return (sks, substTy tvs (map TyVar sks) ty)
skolemize ty = return ([], ty)

newSkolemTyVar :: TyVar -> TC TyVar
newSkolemTyVar tv = do
  i <- newUnique
  return (SkolemTv (Name $ show tv) i)

getFreeTyVars :: [Ty] -> TC [TyVar]
getFreeTyVars ts = do
  ts' <- mapM zonkType ts
  return $ concatMap freeTyVars ts'

substTy :: [TyVar] -> [Ty] -> Ty -> Ty
substTy tvs tys = go (tvs `zip` tys)
  where
    go env (TyVar n) = fromMaybe (TyVar n) (Prelude.lookup n env)
    go env (TyMetaV m) = TyMetaV m
    go env (TyForAll ns t) = let env' = filter (not . (`elem` ns) . fst) env
                             in TyForAll ns (go env' t)
    go env (TyForAllC ns ens t) = let env' = filter (not . (`elem` ens) . fst)
                                        $ filter (not . (`elem` ns) . fst) env
                                  in TyForAllC ns ens (go env' t)
    go env (TyApp t ts) = TyApp t (map (go env) ts)
    go env (TySyn ty ty') = TySyn (go env ty) (go env ty')
