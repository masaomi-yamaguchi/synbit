{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -Wunused-imports #-}

module Synthesis.BxTyping where

import           Syntax.Type
import           Name
import           Control.Monad.Sharing
import           Data.Monadic.List
import           Control.Monad
import qualified Synthesis.LazyEnv as LE
import           Control.Applicative

-- m MTy が非決定的なTypeを表す
data MTy m = MTyApp Bool TName (m (List m (MTy m)))
           | MTyVar TyVar    -- type variable
           | MTyMetaTv Int  -- unify専用
           | MTyForAll Bool [TyVar] (m (MTy m))

instance Monad m => Shareable m TyVar where
  shareArgs _ = return

-- instance Monad m => Convertible m (MTy m) (MTy m)
--  where
--   convert = return
instance Monad m => Convertible m (MTy m) Ty where
  convert (MTyApp _ name mts) = do
    ts <- mts
    ts' <- convert ts
    return (TyApp name ts')
  convert (MTyVar a) = return (TyVar a)
  convert (MTyForAll _ abc mts) = do
    ts <- mts
    ts' <- convert ts
    return (TyForAll abc ts')

instance Monad m => Convertible m Ty (MTy m) where
  convert (TyApp name ts) = return (MTyApp False name (convert ts))
  convert (TyVar a) = return (MTyVar a)
  convert (TyForAll abc ts) = return (MTyForAll False abc (convert ts))
  convert (TyForAllC abc [] ts) = return (MTyForAll False abc (convert ts))

instance Monad m => Shareable m (MTy m) where
  shareArgs f (MTyApp b name tys) =
    if b
    then return (MTyApp True name tys)
    else do
      tys' <- f tys
      return (MTyApp True name tys')
  shareArgs _ (MTyMetaTv i) = return (MTyMetaTv i)
  shareArgs _ (MTyVar a) = return (MTyVar a)
  shareArgs f (MTyForAll b abc ty) =
    if b
    then return (MTyForAll True abc ty)
    else do
      ty' <- f ty
      return (MTyForAll True abc ty')

type MBodyTy m = MTy m

type MBxTy m = MTy m

printList :: Show a => [a] -> IO ()
printList = mapM_ print

mTyB :: Monad m => m (MTy m) -> m (MTy m)
mTyB mty = return $ MTyApp False (TName "BX") (cons mty nil)

mTyArr :: Monad m => m (MTy m) -> m (MTy m) -> m (MTy m)
mTyArr t1 t2 = return $ MTyApp False (TName "->") (cons t1 (cons t2 nil))

mBool :: Monad m => m (MTy m)
mBool = return $ MTyApp False (TName "Bool") nil

mInt :: Monad m => m (MTy m)
mInt = return $ MTyApp False (TName "Int") nil

mChar :: Monad m => m (MTy m)
mChar = return $ MTyApp False (TName "Char") nil

synthesisB :: (MonadPlus m, Sharing m, Delay m) => Int -> Ty -> m (MBxTy m)
synthesisB pen ty = go pen ty True
  where
    go :: (MonadPlus m, Sharing m, Delay m) => Int -> Ty -> Bool -> m (MBxTy m)
    go pen (TyVar a) bx =
      if bx
      then return (MTyVar a) <|> (delay pen $ mTyB (return (MTyVar a)))
      else return (MTyVar a)
    go pen (TyArr t1 t2) bx = if bx
                              then mTyArr (go pen t1 True) (go pen t2 True)
                              else mzero
    go pen (TyApp name tys) bx =
      if bx
      then do
        let tysT = foldr (\ty tys' -> cons (go pen ty True) tys') nil tys
        let tysF = foldr (\ty tys' -> cons (go pen ty False) tys') nil tys
        return (MTyApp False name tysT)
          <|> delay pen (mTyB (return $ MTyApp False name tysF))
      else do
        let tysF = foldr (\ty tys' -> cons (go pen ty False) tys') nil tys
        return (MTyApp False name tysF)
    go pen (TyForAll abc ty) bx = return (MTyForAll False abc (go pen ty bx))   -- abc means forall a b c -- ここのbxは適当に書いた
    go _ _ _ = fail "TyForAllC is not supported by synthesisB"

substM :: (Monad m, Sharing m)
       => m (List m (TyVar, m (MTy m)))
       -> MTy m
       -> m (MTy m)
substM env (MTyApp _ tname ts) = return
  $ MTyApp False tname (mapML (\t -> substM env =<< t) ts)
substM env (MTyVar a) = do
  look <- LE.lookup' a env
  case look of
    Just ty -> ty
    _       -> return (MTyVar a)

-- fun unify (term1, term2) =
--   let fun main [] sigma = SOME sigma
-- 	| main ((T.Var x, t)::rest) sigma = if eqVar (x,t) then main rest sigma
-- 					    else if LU.member x (T.vars t) then NONE
-- 					    else let val rho = [(x,t)]
-- 						 in main (applyE rho rest) (compose rho sigma)
-- 						 end
-- 	| main ((T.Fun (f,ts), T.Fun (g,us))::rest) sigma = if f = g then main (decompose (ts,us) rest) sigma
-- 							    else NONE
-- 	| main ((t,T.Var x)::rest) sigma = main ((T.Var x, t)::rest) sigma
--   in main [(term1,term2)] []
--   end
-- end
--
-- ty1はpoly, ty2はpolyでない
unifiable :: (Monad m, Sharing m) => m (MTy m) -> m (MTy m) -> m Bool
unifiable ty1 ty2 = do
  ty1' <- share (instantiate ty1)
  ty2' <- share ty2
  ans <- unifyL ty1' ty2'
  case ans of
    Nothing -> return False
    Just _  -> return True

-- sigma(ty1) == ty2
-- なるsigmaを探す
-- ty1はinstantiateしないといけない
-- ty2はpolyではだめ
-- ty1, ty2ともにshare済みであることを仮定
--
-- data MTy m = MTyApp TName (m (List m (MTy m)))
--            | MTyVar TyVar    -- type variable
--            | MTyForAll [TyVar] (m (MTy m))
unifyL :: (Monad m, Sharing m)
       => m (MTy m)
       -> m (MTy m)
       -> m (Maybe (m (LE.Env m Int (MTy m)))) -- [(型変数, 型)]を返す

unifyL ty1 ty2 = go LE.empty (Cons (return (ty1, ty2)) nil)
  where
    go :: (Monad m, Sharing m)
       => m (LE.Env m Int (MTy m))
       -> List m (m (MTy m), m (MTy m))
       -> m (Maybe (m (LE.Env m Int (MTy m))))
    go sigma Nil = return (Just sigma)
    go sigma (Cons ty12 rest) = do
      (mty1, mty2) <- ty12
      ty1 <- mty1
      ty2 <- mty2
      case (ty1, ty2) of
        (MTyVar x, MTyVar y) -> if x == y
                                then go sigma =<< rest
                                else return Nothing
        (MTyVar x, _) -> return Nothing
        (MTyMetaTv i, t) -> go (LE.insert i (return t) sigma)
          =<< (applyE i (return t) rest)
        (MTyApp b1 name1 tys1, MTyApp b2 name2 tys2)
          -> if name1 == name2
             then go sigma =<< (decompose tys1 tys2 rest)
             else return Nothing
        (MTyApp b1 name1 tys1, _) -> return Nothing

    apply :: Monad m => Int -> m (MTy m) -> m (MTy m) -> m (MTy m)
    apply i t mty = do
      ty <- mty
      case ty of
        MTyVar a          -> return (MTyVar a)
        MTyMetaTv i'      -> if i == i'
                             then t
                             else return (MTyMetaTv i')
        MTyApp _ name tys -> return (MTyApp False name (mapML (apply i t) tys))

    applyE :: Monad m
           => Int
           -> m (MTy m)
           -> m (List m (m (MTy m), m (MTy m)))
           -> m (List m (m (MTy m), m (MTy m)))
    applyE i t tys = mapML
      (\mty12 -> do
         (ty1, ty2) <- mty12
         return (apply i t ty1, ty2))
      tys

    decompose :: MonadPlus m
              => m (List m (MTy m))
              -> m (List m (MTy m))
              -> m (List m (m (MTy m), m (MTy m)))
              -> m (List m (m (MTy m), m (MTy m)))
    decompose tys1 tys2 l =
      foldrML2 (\ty1 ty2 l' -> cons (return (ty1, ty2)) l') l tys1 tys2

-- MTyMetaTvを含まない前提
instantiate :: (Monad m, Sharing m) => m (MTy m) -> m (MTy m)
instantiate mty = do
  (ans, _) <- instantiate_ mty
  ans

instantiate_ :: (Monad m, Sharing m) => m (MTy m) -> m (m (MTy m), [Int])
instantiate_ mty = do
  ty <- mty
  case ty of
    MTyForAll _ abc ty' -> return
      (go (zip abc [0 ..]) ty', [0 .. (length abc - 1)])
    ty' -> return (return ty', [])
  where
    go :: (Monad m, Sharing m) => [(TyVar, Int)] -> m (MTy m) -> m (MTy m)
    go env mty = do
      ty <- mty
      case ty of
        (MTyApp _ name l) -> return (MTyApp False name (mapML (go env) l))
        (MTyVar a)        -> case lookup a env of
          Just i -> return (MTyMetaTv i)

--
--
-- MetaTvに対するsubst
-- Envは網羅的なことを仮定している
subst :: (Monad m, Sharing m) => m (LE.Env m Int (MTy m)) -> MTy m -> m (MTy m)
subst env (MTyApp _ tname ts) = return
  $ MTyApp False tname (mapML (\t -> subst env =<< t) ts)
subst env (MTyVar a) = return (MTyVar a)
subst env (MTyMetaTv i) = do
  look <- LE.lookup i env
  case look of
    Just ty -> ty
