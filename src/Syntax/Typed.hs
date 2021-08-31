{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

-- {-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -fwarn-missing-signatures #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Syntax.Typed where

import           Data.Foldable (foldrM)
import           Syntax as S
import           Control.Monad.Except
import           Data.List (union, (\\))
import qualified Data.Map as M
import           EnvLike as E
import           Err
import           Name
import           SrcLoc
import qualified Syntax.Type as T
import           Typing as TP
import           Synthesis.PureExpression as P

data Typed a = Typed a T.Ty -- deriving Show

type TExp = Typed Syntax.Typed.Exp

data Exp =
    EVar Name
  | EAbs Name TExp
  | EApp TExp TExp
  | EAdd TExp TExp
  | EEq TExp TExp
  | ELess TExp TExp
  | ENeg TExp
  | ENum Integer
  | EChar Char
  | ELift TExp TExp
  | EAbort TExp
  | ECon Bool Name [TExp] -- BoolはBXかどうかを表す．nameがNTupのとき，Tupleを表す. ユーザ定義の型もnameで管理している
  | ECase TExp [TAlt]
  | ECaseB TExp [TBAlt]
  | EConstL TExp -- !e のこと

  -- deriving Show
type TAlt = (P.Pat, TGuard, TExp)

type TBAlt = (P.Pat, TGuard, TBranch)

type TGuard = TExp

data TBranch =
  TBranch { tBody :: TExp, tExitCond :: TExp, tReconciler :: TExp }
  deriving Show

type HoleEnv = TP.TyEnv

convertToPure :: TExp -> P.Exp
convertToPure (Typed e _) = go e
  where
    go (Syntax.Typed.EVar x) = P.EVar x
    go (Syntax.Typed.EAbs x e) = P.EAbs x (convertToPure e)
    go (Syntax.Typed.EApp e1 e2) = P.EApp (convertToPure e1) (convertToPure e2)
    go (Syntax.Typed.EAdd e1 e2) = P.EAdd (convertToPure e1) (convertToPure e2)
    go (Syntax.Typed.EEq e1 e2) = P.EEq (convertToPure e1) (convertToPure e2)
    go (Syntax.Typed.ELess e1 e2) =
      P.ELess (convertToPure e1) (convertToPure e2)
    go (Syntax.Typed.ENeg e1) = P.ENeg (convertToPure e1)
    go (Syntax.Typed.ENum i) = P.ENum i
    go (Syntax.Typed.EChar c) = P.EChar c
    go (Syntax.Typed.ELift e1 e2) =
      P.ELift (convertToPure e1) (convertToPure e2)
    go (Syntax.Typed.EAbort e1) = P.EAbort (convertToPure e1)
    go (Syntax.Typed.ECon b name es) = P.ECon b name (map convertToPure es)
    go (Syntax.Typed.ECase e0 alts) =
      P.ECase (convertToPure e0) (map goAlt alts)
    go (Syntax.Typed.ECaseB e0 balts) =
      P.ECaseB (convertToPure e0) (map goBAlt balts)
    go (Syntax.Typed.EConstL e) = P.EConstL (convertToPure e)

    goAlt :: Syntax.Typed.TAlt -> P.Alt
    goAlt (p, g, e) = (p, convertToPure g, convertToPure e)

    goBAlt :: Syntax.Typed.TBAlt -> P.BAlt
    goBAlt (p, g, br) =
      ( p
      , convertToPure g
      , P.Branch { P.body = convertToPure $ tBody br
                 , P.exitCond = convertToPure $ tExitCond br
                 , P.reconciler = convertToPure $ tReconciler br
                 })

instance Show Syntax.Typed.Exp where
  show = showTExpGo

instance Show a => Show (Typed a) where
  show (Typed e ty) = show e ++ " :: " ++ show ty

showTExp :: TExp -> String
showTExp (Typed e ty) = showTExpGo e ++ " :: " ++ show ty

showTExpBr :: TExp -> String
showTExpBr (Typed e ty) = showTB $ showTExpGo e
  where
    showTB :: String -> String
    showTB s = "(" ++ s ++ " :: " ++ show ty ++ ")"

showTExpGo :: Syntax.Typed.Exp -> String
showTExpGo e = case e of
  Syntax.Typed.EVar name -> show name
  Syntax.Typed.EAbs name e1 -> "\\" ++ show name ++ " -> " ++ showTExpBr e1
  Syntax.Typed.EApp e1 e2 -> showTExpBr e1 ++ " " ++ showTExpBr e2
  Syntax.Typed.EAdd e1 e2 -> showTExpBr e1 ++ " + " ++ showTExpBr e2
  Syntax.Typed.EEq e1 e2 -> showTExpBr e1 ++ " == " ++ showTExpBr e2
  Syntax.Typed.ELess e1 e2 -> showTExpBr e1 ++ " < " ++ showTExpBr e2
  Syntax.Typed.ENeg e1 -> "-" ++ showTExpBr e1
  Syntax.Typed.ENum i -> show i
  Syntax.Typed.EChar c -> show c
  Syntax.Typed.ELift e1 e2 -> "lift " ++ showTExpBr e1 ++ " " ++ showTExpBr e2
  Syntax.Typed.EAbort e1 -> "abort " ++ showTExpBr e1
  Syntax.Typed.ECon False NNil [] -> "[]"
  Syntax.Typed.ECon True NNil [] -> "![]"
  Syntax.Typed.ECon b NCons [e1, l]
    -> (case showTNCons l of
          Just text -> if b
                       then "[* " ++ showTExp e1 ++ text ++ " *]"
                       else "[" ++ showTExp e1 ++ text ++ "]"
          Nothing   -> showTExpBr e1
            ++ (if b
                then " :* "
                else " : ")
            ++ showTNCons2 l)
  Syntax.Typed.ECon False NTup (e1:es)
    -> "(" ++ showTExp e1 ++ concatMap (\e -> ", " ++ showTExp e) es ++ ")"
  Syntax.Typed.ECon True NTup (e1:es)
    -> "(* " ++ showTExp e1 ++ concatMap (\e -> ", " ++ showTExp e) es ++ " *)"
  Syntax.Typed.ECon False name es -> show name
    ++ concatMap (\e -> " " ++ showTExpBr e) es
  Syntax.Typed.ECon True name es
    -> show name ++ "*" ++ concatMap (\e -> " " ++ showTExpBr e) es
  Syntax.Typed.ECase e1 alts
    -> "case " ++ showTExpBr e1 ++ " of { " ++ showTAlts alts ++ " }"
  Syntax.Typed.ECaseB e1 alts
    -> "case* " ++ showTExpBr e1 ++ " of { " ++ showTBAlts alts ++ " }"
  Syntax.Typed.EConstL e1 -> "!" ++ showTExpBr e1

showTAlts :: [TAlt] -> String
showTAlts [] = ""
showTAlts (a:alts) = go a ++ concatMap (\a -> ", " ++ go a) alts
  where
    go (p, g, e) =
      P.showPat False p ++ " | " ++ showTExp g ++ " => " ++ showTExp e

showTBAlts :: [TBAlt] -> String
showTBAlts [] = ""
showTBAlts (a:alts) = go a ++ concatMap (\a -> ", " ++ go a) alts
  where
    go (p, g, TBranch e cond reconcile) = P.showPat False p
      ++ " | "
      ++ showTExp g
      ++ " => "
      ++ showTExp e
      ++ " with "
      ++ showTExpBr cond
      ++ " reconciled by "
      ++ showTExpBr reconcile

showTNCons :: TExp -> Maybe String
showTNCons (Typed (Syntax.Typed.ECon _ NNil []) ty) = Just ""
showTNCons (Typed (Syntax.Typed.ECon _ NCons [e, l]) ty) = do
  tl <- showTNCons l
  return $ ", " ++ showTExp e ++ tl
showTNCons e = Nothing

showTNCons2 :: TExp -> String
showTNCons2 (Typed (Syntax.Typed.ECon b NNil []) ty) =
  if b
  then "(| [] :: " ++ show ty ++ "|)"
  else "([] ::" ++ show ty ++ ")" -- unused?
showTNCons2 (Typed (Syntax.Typed.ECon b NCons [e, l]) ty) =
  if b
  then showTExpBr e ++ " :* " ++ showTNCons2 l
  else showTExpBr e ++ " : " ++ showTNCons2 l
showTNCons2 e = showTExpBr e

-- showTPat :: Bool -> TPat -> String
-- showTPat b (TPat p env) = go b p ++ " ... " ++ showTyEnv env
--   where
--     go b p = case p of
--       Syntax.Typed.PNum i -> show i
--       Syntax.Typed.PChar c -> show c
--       Syntax.Typed.PVar name -> show name
--       Syntax.Typed.PCon NNil [] -> "[]"
--       Syntax.Typed.PCon NCons [p1, l]
--         -> if b
--            then "(" ++ go True p1 ++ " : " ++ go False l ++ ")"
--            else go True p1 ++ " : " ++ go False l
--       Syntax.Typed.PCon NTup (p1:ps)
--         -> "(" ++ go False p1 ++ concatMap (\p -> ", " ++ go False p) ps ++ ")"
--       Syntax.Typed.PCon name ps
--         -> if b
--            then "("
--              ++ show name
--              ++ concatMap (\p -> " " ++ go True p) ps
--              ++ ")"
--            else show name ++ concatMap (\p -> " " ++ go True p) ps
testTypedExp :: TExp
testTypedExp =
  Typed (Syntax.Typed.EVar (Name "x")) (T.TyVar (T.BoundTv (Name "a")))

getType :: TExp -> T.Ty
getType (Typed e ty) = ty

convertPat :: T.LPat -> P.Pat
convertPat lp = go (unLoc lp)
  where
    go :: T.Pat -> P.Pat
    go (T.PNum i) = P.PNum i
    go (T.PChar c) = P.PChar c
    go (T.PVar name) = P.PVar name
    go (T.PCon name lpats) = P.PCon name $ map (go . unLoc) lpats

-- convertPatL :: P.Pat -> T.LPat
-- convertPatL p = noLoc (go p)
--   where
--     go :: P.Pat -> T.Pat
--     go (P.PNum i) = T.PNum i
--     go (P.PChar c) = T.PChar c
--     go (P.PVar name) = T.PVar name
--     go (P.PCon name pats) = T.PCon name $ map (noLoc . go) pats
type BodyTExp = MonoTExp  -- forall body. only consider rank 1

type PolyTExp = TExp      -- polymorphic types

type MonoTExp = TExp      -- monomorphic types

inferDeclToTExp :: T.Decl -> (TyEnv, Synonyms) -> UniqSupply -> IO (Err TExp)
inferDeclToTExp (T.Decl name mty lexp) (env, syn) ref = convertResult
  <$> runTC
    (zonkTExp =<< inferPolyTExp mty lexp)
    TcEnv { tcTyEnv = env
          , tcBxTyEnv = E.empty
          , tcUniqRef = ref
          , tcSynonyms = syn
          }

zonkTExp :: TExp -> TC TExp
zonkTExp (Typed e ty) = do
  ty' <- zonkType ty
  e' <- go e
  return (Typed e' ty')
  where
    go :: Syntax.Typed.Exp -> TC Syntax.Typed.Exp
    go (Syntax.Typed.EVar name) = return $ Syntax.Typed.EVar name
    go (Syntax.Typed.EAbs name e) = do
      e' <- zonkTExp e
      return (Syntax.Typed.EAbs name e')
    go (Syntax.Typed.EApp e1 e2) = do
      e1' <- zonkTExp e1
      e2' <- zonkTExp e2
      return (Syntax.Typed.EApp e1' e2')
    go (Syntax.Typed.EAdd e1 e2) = do
      e1' <- zonkTExp e1
      e2' <- zonkTExp e2
      return (Syntax.Typed.EAdd e1' e2')
    go (Syntax.Typed.EEq e1 e2) = do
      e1' <- zonkTExp e1
      e2' <- zonkTExp e2
      return (Syntax.Typed.EEq e1' e2')
    go (Syntax.Typed.ELess e1 e2) = do
      e1' <- zonkTExp e1
      e2' <- zonkTExp e2
      return (Syntax.Typed.ELess e1' e2')
    go (Syntax.Typed.ENeg e) = do
      e' <- zonkTExp e
      return (Syntax.Typed.ENeg e')
    go (Syntax.Typed.ENum i) = return (Syntax.Typed.ENum i)
    go (Syntax.Typed.EChar c) = return (Syntax.Typed.EChar c)
    go (Syntax.Typed.ELift e1 e2) = do
      e1' <- zonkTExp e1
      e2' <- zonkTExp e2
      return (Syntax.Typed.ELift e1' e2')
    go (Syntax.Typed.EAbort e) = do
      e' <- zonkTExp e
      return (Syntax.Typed.EAbort e')
    go (Syntax.Typed.ECon b n es) = do
      es' <- mapM zonkTExp es
      return (Syntax.Typed.ECon b n es')
    go (Syntax.Typed.ECase e alts) = do
      e' <- zonkTExp e
      alts' <- mapM
        (\(p, g, e) -> do
           g' <- zonkTExp g
           e' <- zonkTExp e
           return (p, g', e'))
        alts
      return (Syntax.Typed.ECase e' alts')
    go (Syntax.Typed.ECaseB e0 alts) = do
      e0' <- zonkTExp e0
      alts' <- mapM
        (\(p, g, TBranch e cond reconcile) -> do
           g' <- zonkTExp g
           e' <- zonkTExp e
           cond' <- zonkTExp cond
           reconcile' <- zonkTExp reconcile
           return (p, g', TBranch e' cond' reconcile'))
        alts
      return (Syntax.Typed.ECaseB e0' alts')
    go (Syntax.Typed.EConstL e) = do
      e' <- zonkTExp e
      return (Syntax.Typed.EConstL e')

vmapM :: (T.Ty -> TC T.Ty) -> TyEnv -> TC TyEnv
vmapM f env = do
  let envL = toList env
  envL' <- mapM
    (\(x, ty) -> do
       ty' <- f ty
       return (x, ty'))
    envL
  return $ fromList envL'

inferBodyTExp :: Maybe T.PolyTy -> T.LExp -> TC BodyTExp
inferBodyTExp Nothing le = do
  ty <- newMetaTy (getLoc le)
  checkBodyTExp le ty
inferBodyTExp (Just mty) le = do
  ty <- newMetaTy (getLoc le)
  e' <- checkBodyTExp le ty
  mty' <- instantiate noSrcSpan mty
  unify noSrcSpan mty' ty
  return e'

-- mtyは,ユーザに型を指定されたときに使う
inferPolyTExp :: Maybe T.PolyTy -> T.LExp -> TC PolyTExp
inferPolyTExp mty e = do
  e' <- inferBodyTExp mty e
  envTyps <- getEnvTypes
  envTvs <- getMetaTyVars envTyps
  expTvs <- getMetaTyVarsTExp e'
  let forallTvs = expTvs \\ envTvs
  quantifyTExp forallTvs e'

getMetaTyVarsTExp :: TExp -> TC [T.MetaTv]
getMetaTyVarsTExp e = do
  (Typed e' ty) <- zonkTExp e
  tv <- getMetaTyVars [ty]
  case e' of
    Syntax.Typed.EVar name       -> return tv
    Syntax.Typed.EAbs name e1    -> do
      tv1 <- getMetaTyVarsTExp e1
      return $ union tv tv1
    Syntax.Typed.EApp e1 e2      -> do
      tv1 <- getMetaTyVarsTExp e1
      tv2 <- getMetaTyVarsTExp e2
      return $ union tv $ union tv1 tv2
    Syntax.Typed.EAdd e1 e2      -> do
      tv1 <- getMetaTyVarsTExp e1
      tv2 <- getMetaTyVarsTExp e2
      return $ union tv $ union tv1 tv2
    Syntax.Typed.EEq e1 e2       -> do
      tv1 <- getMetaTyVarsTExp e1
      tv2 <- getMetaTyVarsTExp e2
      return $ union tv $ union tv1 tv2
    Syntax.Typed.ELess e1 e2     -> do
      tv1 <- getMetaTyVarsTExp e1
      tv2 <- getMetaTyVarsTExp e2
      return $ union tv $ union tv1 tv2
    Syntax.Typed.ENeg e1         -> return tv
    Syntax.Typed.ENum i          -> return tv
    Syntax.Typed.EChar c         -> return tv
    Syntax.Typed.ELift e1 e2     -> do
      tv1 <- getMetaTyVarsTExp e1
      tv2 <- getMetaTyVarsTExp e2
      return $ union tv $ union tv1 tv2
    Syntax.Typed.EAbort e1       -> do
      tv1 <- getMetaTyVarsTExp e1
      return $ union tv tv1
    Syntax.Typed.ECon b n es     -> do
      tv_ts <- foldrM
        (\e ret -> do
           tv <- getMetaTyVars [getType e]
           return $ union tv ret)
        tv
        es
      return $ union tv tv_ts
    Syntax.Typed.ECase e1 alts   -> do
      tv1 <- getMetaTyVarsTExp e1
      return $ union tv tv1
    Syntax.Typed.ECaseB e1 balts -> do
      tv1 <- getMetaTyVarsTExp e1
      return $ union tv tv1
    Syntax.Typed.EConstL e1      -> do
      tv1 <- getMetaTyVarsTExp e1
      return $ union tv tv1

quantifyTExp :: [T.MetaTv] -> TExp -> TC PolyTExp
quantifyTExp tvs e = do
  mapM_ bind (tvs `zip` newBinders)
  (Typed e' ty) <- zonkTExp e
  return (Typed e' (TyForAll newBinders ty))
  where
    usedBinders = tyVarBindersTExp e

    newBinders = take (length tvs) (allFancyBinders \\ usedBinders)

    bind (metav, typev) = writeTv metav (TyVar typev)

    tyVarBindersTExp :: TExp -> [T.TyVar]
    tyVarBindersTExp (Typed e ty) =
      let bs = tyVarBinders ty
      in case e of
           Syntax.Typed.EVar n          -> bs
           Syntax.Typed.EAbs n e1       -> union bs $ tyVarBindersTExp e1
           Syntax.Typed.EApp e1 e2
             -> union bs $ tyVarBindersTExp e1 `union` tyVarBindersTExp e2
           Syntax.Typed.EAdd e1 e2
             -> union bs $ tyVarBindersTExp e1 `union` tyVarBindersTExp e2
           Syntax.Typed.EEq e1 e2
             -> union bs $ tyVarBindersTExp e1 `union` tyVarBindersTExp e2
           Syntax.Typed.ELess e1 e2
             -> union bs $ tyVarBindersTExp e1 `union` tyVarBindersTExp e2
           Syntax.Typed.ENeg e1         -> union bs $ tyVarBindersTExp e1
           Syntax.Typed.ENum n          -> bs
           Syntax.Typed.EChar n         -> bs
           Syntax.Typed.ELift e1 e2
             -> union bs $ tyVarBindersTExp e1 `union` tyVarBindersTExp e2
           Syntax.Typed.EAbort e1       -> union bs $ tyVarBindersTExp e1
           Syntax.Typed.ECon b n es     -> union bs
             $ foldr (\e ret -> union ret $ tyVarBindersTExp e) [] es
           Syntax.Typed.ECase e1 alts   -> union bs $ tyVarBindersTExp e1
           Syntax.Typed.ECaseB e1 balts -> union bs $ tyVarBindersTExp e1
           Syntax.Typed.EConstL e1      -> union bs $ tyVarBindersTExp e1

checkBodyTExp :: T.LExp -> T.BodyTy -> TC TExp
checkBodyTExp (L span e) expectedTy = do
  liftIO $ putStrD $ "Checking " ++ show e ++ " against " ++ show expectedTy
  go e
  where
    go :: T.Exp -> TC TExp
    go (T.EVar x) = do
      tx <- lookupVar span x
      instPoly span tx expectedTy
      return $ Typed (Syntax.Typed.EVar x) expectedTy
    go (T.EAbs x e) = do
      (argTy, resTy) <- ensureFunType span expectedTy
      e' <- extendLocal x argTy $ checkBodyTExp e resTy
      return $ Typed (Syntax.Typed.EAbs x e') expectedTy
    -- let多相もどき
    -- なんか面倒くさくなりそうなので省略
    -- 実装はできている
    -- go (S.EApp (L span' (S.EAbs x e2)) e1) = do
    --   e1' <- inferPolyTExp Nothing e1
    --   e2' <- extendLocal x (getType e1') $ checkBodyTExp e2 expectedTy
    --   let abs' = Typed (EAbs x e2') (TyArr (getType e1') (getType e2'))
    --   return $ Typed (EApp abs' e1') expectedTy
    go (T.EApp e1 e2) = do
      e1' <- inferBodyTExp Nothing e1
      (argTy, resTy) <- ensureFunType span (getType e1')
      e2' <- checkBodyTExp e2 argTy
      unify span resTy expectedTy
      return $ Typed (Syntax.Typed.EApp e1' e2') expectedTy
    go (T.EAdd e1 e2) = do
      ensureBaseType span TyInt expectedTy
      e1' <- checkBodyTExp e1 TyInt
      e2' <- checkBodyTExp e2 TyInt
      return $ Typed (Syntax.Typed.EAdd e1' e2') expectedTy
    -- 怪しい実装．関数を比較していてもお咎め無し
    -- 試したところ，実行時エラーになった
    go (T.EEq e1 e2) = do
      ensureBaseType span TyBool expectedTy
      ty <- newMetaTy span
      e1' <- checkBodyTExp e1 ty
      e2' <- checkBodyTExp e2 ty
      return $ Typed (Syntax.Typed.EEq e1' e2') expectedTy
    go (T.ELess e1 e2) = do
      ensureBaseType span TyBool expectedTy
      e1' <- checkBodyTExp e1 TyInt
      e2' <- checkBodyTExp e2 TyInt
      return $ Typed (Syntax.Typed.ELess e1' e2') expectedTy
    go (T.ENeg e) = do
      ensureBaseType span TyInt expectedTy
      e' <- checkBodyTExp e TyInt
      return $ Typed (Syntax.Typed.ENeg e') expectedTy
    go (T.ENum n) = do
      ensureBaseType span TyInt expectedTy
      return $ Typed (Syntax.Typed.ENum n) expectedTy
    go (T.EChar e) = do
      ensureBaseType span TyChar expectedTy
      return $ Typed (Syntax.Typed.EChar e) expectedTy
    go (T.ELift e1 e2) = do
      (argTy, resTy) <- ensureFunType span expectedTy
      argTy' <- ensureBxType span argTy
      resTy' <- ensureBxType span resTy
      e1' <- checkBodyTExp e1 (argTy' --> resTy')
      e2' <- checkBodyTExp e2 (argTy' --> resTy' --> argTy')
      return $ Typed (Syntax.Typed.ELift e1' e2') expectedTy
    go (T.EAbort e) = do
      e' <- checkBodyTExp e (TyList TyChar)
      return $ Typed (Syntax.Typed.EAbort e') (TyList TyChar)
    go (T.ECon b NTup es) = do
      expectedTy' <- if b
                     then ensureBxType span expectedTy
                     else return expectedTy
      ts <- ensureTupType span (length es) expectedTy'
      es' <- zipWithM
        (\e t -> checkBodyTExp
           e
           (if b
            then TyB t
            else t))
        es
        ts
      return $ Typed (Syntax.Typed.ECon b NTup es') expectedTy
    go (T.ECon b cname es) = do
      conTy <- instantiate span =<< lookupVar span cname
      ty <- convertTy b conTy
      (retTy, es') <- foldM app (ty, []) es
      unify span retTy expectedTy
      return $ Typed (Syntax.Typed.ECon b cname (reverse es')) expectedTy -- このreverse es'は正しいreverse
      where
        -- convertTy converts a -> b -> c to BX a -> BX b -> BX c for example
        convertTy False t = return t
        convertTy True (T.TyArr t1 t2) =
          liftM2 (-->) (convertArg t1) (convertTy True t2)
        convertTy True ty = return $ TyB ty

        convertArg t = return $ TyB t

        app :: (T.MonoTy, [TExp]) -> T.LExp -> TC (T.MonoTy, [TExp])
        app (ty, ts) e = do
          (argTy, resTy) <- ensureFunType span ty
          e' <- checkBodyTExp e argTy
          return (resTy, e':ts)
    go (T.ECase e0 alts) = do
      (tpat, alts') <- checkAltsTExp alts expectedTy
      e0' <- checkBodyTExp e0 tpat
      return $ Typed (Syntax.Typed.ECase e0' alts') expectedTy
    go (T.ECaseB e0 alts) = do
      expectedTyUnB <- ensureBxType span expectedTy
      (tpat, alts') <- checkBAltsTExp alts expectedTyUnB
      e0' <- checkBodyTExp e0 (TyB tpat)
      return $ Typed (Syntax.Typed.ECaseB e0' alts') expectedTy
    go (T.EConstL e) = do
      ty <- ensureBxType span expectedTy
      e' <- checkBodyTExp e ty
      return $ Typed (Syntax.Typed.EConstL e') expectedTy

checkAltsTExp :: [(T.LPat, T.LGuard, T.LExp)]
              -> T.MonoTy
              -> TC (T.MonoTy, [(P.Pat, TGuard, TExp)])
checkAltsTExp [] expectedTy = do
  a <- newMetaTy noSrcSpan
  return (a, [])
checkAltsTExp ((p, g, e):alts) expectedTy = do
  (tpat, env) <- inferP p
  g' <- extendAllLocal env $ checkBodyTExp g TyBool
  e' <- extendAllLocal env $ checkBodyTExp e expectedTy
  (tpat', alts') <- checkAltsTExp alts expectedTy
  unify (getLoc p) tpat tpat'
  let p' = convertPat p
  return (tpat, (p', g', e'):alts')

checkBAltsTExp :: [(T.LPat, T.LGuard, T.Branch)]
               -> T.MonoTy
               -> TC (T.MonoTy, [(P.Pat, TGuard, TBranch)])
checkBAltsTExp [] expectedTyUnB = do
  a <- newMetaTy noSrcSpan
  return (a, [])
checkBAltsTExp ((p, g, T.Branch e cond reconcile):alts) expectedTyUnB = do
  (tpat, env) <- inferP p
  g' <- extendAllLocal env $ checkBodyTExp g TyBool
  cond' <- checkBodyTExp cond (expectedTyUnB --> TyBool)
  reconcile' <- checkBodyTExp reconcile (tpat --> expectedTyUnB --> tpat)
  e' <- extendBxAllLocal env $ checkBodyTExp e (TyB expectedTyUnB)
  (tpat', alts') <- checkBAltsTExp alts expectedTyUnB
  unify (getLoc p) tpat tpat'
  let p' = convertPat p
  return (tpat, (p', g', TBranch e' cond' reconcile'):alts')

newtype TExpEnv = TE (M.Map Name TExp)
  deriving (EnvLike Name TExp)

defaultTExpEnv :: TExpEnv
defaultTExpEnv = E.empty

