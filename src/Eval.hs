{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}

module Eval (defaultEnv, toEnv, Env, eval, evalAsUsual, evalAsLens) where

import           Control.Category (id, (.))
import           Control.Monad ((<=<), liftM2, zipWithM, foldM, MonadPlus(..))
import           Control.Monad.Reader (ReaderT, ask, local, runReaderT)
import           Control.Monad.Trans (lift)
import qualified Data.Map as M
import           Data.Maybe (fromJust, isNothing)
import           Debug.Trace (trace)
import           Prelude hiding (id, (.))
import           Control.Monad.Except (throwError)
import           Util
import           Name
import           SrcLoc
import           Loc
import           E
import           Err
import           EnvLike as E
import           Value
import           Syntax
import           Lens
import           RunTimeException

newtype Env = Env (M.Map Name Value)
  deriving (EnvLike Name Value)

instance Show Env where
  show (Env m) = "ENV: \n"
    ++ foldr
      (\(k, v) r -> adjustWidth (show k) ++ " -> " ++ show v ++ "\n" ++ r)
      ""
      (M.toList m)
    where
      adjustWidth s = take maxKeyLen $ s ++ cycle " "

      maxKeyLen = foldr max 0 $ map (length . show) $ M.keys m

toEnv :: Env -> Prog -> Env
toEnv oenv ds = env
  where
    env = go ds

    go [] = oenv
    go (L _ (Decl n _ e):ds) = insert n (runE' initLoc $ eval e env) (go ds)

    runE' l x = case runE l x of
      Ok x  -> x
      Bad s -> rtError s

    fromRight (Right a) = a
    fromRight (Left s) = rtError s

defaultEnv :: Env
defaultEnv = Env
  (M.fromList
     [ (Name "inspect", pInspect)
     , (Name "comp", pComp)
     , (Name "orElse", pOrElse)
     , (Name "showInt", pShowInt)])

pShowInt :: Value
pShowInt = VFun
  $ \_ v -> case v of
    VNum n -> return
      $ foldr (\a b -> VCon NCons [VChar a, b]) (VCon NNil []) (show n)
    _
      -> throwError $ "The argument of showInt must be a number: " ++ show v

pComp :: Value
pComp = VFun
  $ \k1 v1 -> return
  $ VFun
  $ \k2 v2 -> case (v1, v2) of
    (VFun f, VFun g) -> return
      $ VFun
        (\k3 v3 -> do
           v' <- g k3 v3
           f k3 v')
    (_, _)           -> throwError
      $ "Both operands of \".\" must be functions: " ++ show (v1, v2)

pOrElse :: Value
pOrElse = VFun
  $ \_ v1 -> return
  $ VFun
  $ \_ v2 -> return
  $ case (v1, v2) of
    (VTrue, _) -> VTrue
    _          -> v2

pInspect :: Value
pInspect = VFun
  $ \_ v -> case v of
    VBX b -> return $ VBX (fromGetPut get put . b)
    _     -> throwError $ "The argument of inspect must be bidirectional."
  where
    get x = trace ("in get: " ++ show x) x

    put x x' = trace ("in put: " ++ show x ++ " --> " ++ show x') x'

lookupL' :: Loc -> Lens Store Value
lookupL' k = fromPartialGetPut g p
  where
    g :: Store -> Err Value
    g s = case E.lookup k s of
      Just v  -> return v
      Nothing -> throwError $ "Undefined reference: " ++ show k

    p :: Store -> Value -> Err Store
    p _ v = return $ insert k v empty

lookupL :: Loc -> Lens Store (Maybe Value)
lookupL k = fromGetPut
  g
  (\_ v -> case v of
     Just u  -> insert k u empty
     Nothing -> empty)
  where
    g :: Store -> Maybe Value
    g s   -- trace ("looking up " ++ show k ++ " from " ++ show s)
      = E.lookup k s

safeInsert
  :: (Show e, Show k, Show v, EnvLike k v e) => String -> k -> v -> e -> e
safeInsert msg k v e = case E.lookup k e of
  Just _ -> rtError
    $ msg
    ++ "Already filled: inserting "
    ++ show k
    ++ " "
    ++ show v
    ++ " to "
    ++ show e
  _      -> insert k v e

tupleL :: String -> [Lens Store a] -> Lens Store [a]
tupleL msg lenses = fromPartialGetPut g p
  where
    g s = mapM (\l -> get l s) lenses

    p s vs = do
      ss <- zipWithM (\l v -> put l s v) lenses vs
      foldM (\m1 m2 -> mergeStoreM msg m1 m2) empty ss

pairL :: String -> Lens Store a -> Lens Store b -> Lens Store (a, b)
pairL msg l1 l2 = fromPartialGetPut g p
  where
    g s = (,) <$> get l1 s <*> get l2 s

    p s (a, b) = do
      s1 <- put l1 s a
      s2 <- put l2 s b
      mergeStoreM msg s1 s2

constL :: Show i => i -> Value -> Lens Store Value
constL i v = fromPartialGetPut (const $ return v) (const r)
  where
    r :: Value -> Err Store
    r v'
      | v `equal` v' = return empty
    r v' = throwError
      $ "Update on constant: "
      ++ show i
      ++ "\n"
      ++ "  expected: "
      ++ show v
      ++ "\n  received: "
      ++ show v'
      ++ "."

conL :: Show i => i -> Name -> Int -> Lens [Value] Value
conL i n arity = fromPartialGetPut g p
  where
    g vs = return $ VCon n vs

    p :: [Value] -> Value -> Err [Value]
    p _ (VCon m rs)
      | m == n = return rs
    p _ v = throwError
      $ "Update on constant: "
      ++ show i
      ++ "\n  expected: "
      ++ show n
      ++ "..."
      ++ "\n  received: "
      ++ show v

evalToFO e env = do
  v <- eval e env
  if isFO v
    then return v
    else throwError $ "Must be first-order: " ++ showEV e v

evalToBX :: LExp -> Env -> E (Lens Store Value)
evalToBX e env = do
  v <- eval e env
  case v of
    VBX lens -> return lens
    _        -> throwError $ "Must be bidirectional: " ++ showEV e v

-- | Evaluate an expression, unidirectionally
eval :: LExp -> Env -> E Value
eval (L i e) env = eval_ i e env

eval_ :: SrcSpan -> Exp -> Env -> E Value
eval_ i (EVar x) env = case E.lookup x env of
  Just v  -> return v
  Nothing
    -> throwError $ "Undefined variable: " ++ show x ++ " in " ++ show env
eval_ i (EAbs x e) env = do
  hp <- ask
  return
    $ VFun
      (\k v -> if k < hp
               then throwError "Function is called in smaller context"
               else local (const k) $ eval e (insert x v env))
eval_ i (EApp e1 e2) env = do
  hp <- ask
  f <- eval e1 env
  v <- eval e2 env
  case f of
    VFun f -> f hp v
    _      -> throwError $ "Cannot apply non functions: " ++ showEV e1 f
eval_ i (ENum k) env = return $ VNum k
eval_ i (EChar k) env = return $ VChar k
eval_ i (EAdd e1 e2) env = do
  v1 <- eval e1 env
  v2 <- eval e2 env
  case (v1, v2) of
    (VNum k1, VNum k2) -> return $ VNum $ k1 + k2
    _ -> throwError
      $ "Both operand of + must be first-order values: "
      ++ show v1
      ++ ", "
      ++ show v2
eval_ i (EEq e1 e2) env = do
  v1 <- evalToFO e1 env
  v2 <- evalToFO e2 env
  return
    (if equal v1 v2
     then VTrue
     else VFalse)
eval_ i (ELess e1 e2) env = do
  v1 <- evalToFO e1 env
  v2 <- evalToFO e2 env
  return
    (if less v1 v2
     then VTrue
     else VFalse)
eval_ i (EAbort e) env = do
  v <- eval e env
  throwError $ "Aborted: " ++ toString v
  where
    toString (VCon NNil []) = ""
    toString (VCon NCons [VChar c, r]) = c:toString r
    toString _ = undefined
eval_ i (ENeg e) env = do
  v <- eval e env
  case v of
    VNum k -> return $ VNum (-k)
    _      -> throwError $ "Only numebers can be negated: " ++ show v
-- eval_ i e@(EDiscard x e1 e2) env = do
--   start <- ask
--   u  <- evalToFO e1 env
--   bx <- local (+1) (evalToBX e2 (insert x (VBX $ lookupL start) env))
--   case E.lookup x env of
--         Just (VBX bx2) ->
--           return $ VBX (restoreL bx start u bx2)
--         Just v ->
--           err $ "Variable " ++ show x ++ " is assigned to non bidirectional value: " ++ show v
--         Nothing ->
--           err $ "Undefined variable: " ++ show x
--
--   where
--     restoreL :: Lens Store (Maybe Value) -> Loc -> Value ->
--                 Lens Store (Maybe Value) -> Lens Store (Maybe Value)
--     restoreL bx start u bx2 = fromGetPut g p
--       where
--         g store   = do
--           u' <- get bx2 store
--           get bx (safeInsert "[default]" start u' store)
--         p store v =
--           let store' = case get bx2 store of
--                 Just u' -> safeInsert "[default]" start u' store
--                 Nothing -> store -- insert start u  store
--               store'' = put bx store' v
--               upd     = E.lookup start store''
--                         `mplus` E.lookup start store' -- use original value
--                         `mplus` Just u                -- use default  value
--           in (if isNothing (E.lookup start store'') && isNothing (E.lookup start store') then
--                 trace ("variable " ++ show x ++ " is restored as " ++ show upd)
--               else
--                 id) $
--              mergeStore (showIE i e) (delete start store'') (put bx2 store upd)
-- eval_ i exp@(EIfEq x y e) env = do
--   start <- ask
--   let Just (VBX bxx) = E.lookup x env
--   let Just (VBX bxy) = E.lookup y env
--   VFun k   <- (eval e env)
--   VFun kx  <- k  start (VBX $ lookupL $ start )
--   VBX  bxk <- kx (start+2) (VBX $ lookupL $ start + 1)
--   return $ VBX $ makeLens bxx bxy bxk start
--                . pairL (showIE i exp) id (pairL (showIE i exp) bxx bxy)
--   where
--     makeLens bxx bxy bxk start = fromGetPut g p
--       where
--         insXY :: Maybe Value -> Maybe Value -> Store -> Store
--         insXY (Just vx) (Just vy) store =
--           if vx `equal` vy then
--             safeInsert "[eq]" start (VRight (VTup [])) $ safeInsert "[eq]" (start+1) vy $ store
--           else
--             safeInsert "[eq]" start (VLeft  vx)        $ safeInsert "[eq]" (start+1) vy $ store
--         insXY Nothing (Just vy) store =
--           safeInsert "[eq]" (start + 1) vy store
--         insXY _ _ store = store
--
--
--         g :: (Store, (Maybe Value, Maybe Value)) -> Maybe Value
--         g (store, (x, y)) =
--           get bxk (insXY x y store)
--
-- --        p [store, x, y] Nothing = Nothing
--         p (store, (x, y)) u =
--           let store'  = insXY x y store
--               store'' = put bxk store' u
--               vy      = E.lookup (start+1) store''
--           in trace ("VY> " ++  show vy) $
--            case vy of
--              Nothing ->
--                rtError "The second argument must not be unspecified value."
--              Just vy' ->
--                case maybe (VRight (VTup [])) id $ E.lookup start store'' of
--                  VRight (VTup []) ->
--                    (delete start $ delete (start+1) $ store'',
--                     (vy,vy))
--                  VLeft vx ->
--                    if vx `equal` vy' then
--                      rtError "Unequality constraint violated"
--                    else
--                      (delete start $ delete (start+1) $ store'',
--                       (Just vx, vy))
--                  _ -> rtError "Type error"
eval_ i (ECon False n es) env = do
  vs <- mapM (\e -> eval e env) es
  return $ VCon n vs
eval_ i e@(ECon True n es) env = do
  bxs <- mapM (\e -> evalToBX e env) es
  return $ VBX $ conL i n (length bxs) . tupleL (showIE i e) bxs
eval_ i (ELift e1 e2) env = do
  hp <- ask
  return
    $ VFun
    $ \_ v -> case v of
      VBX l -> return $ VBX $ makeLens hp e1 e2 . l
      _     -> throwError $ "Argument must be bidirectionals: " ++ show v
  where
    makeLens :: HeapPointer -> LExp -> LExp -> Lens Value Value
    makeLens hp e1 e2 = fromPartialGetPut g p
      where
        g = evalAsFOFunc hp e1 env

        apply hp (VFun f) s = f hp s
        apply hp v s = throwError "Put must be a binary function"

        p s v = runE hp
          $ do
            v1 <- eval e2 env
            v2 <- apply hp v1 s
            apply hp v2 v
eval_ i (EConstL e) env = do
  v <- evalToFO e env
  return $ VBX (constL i v)
eval_ i (ECase e0 alts) env = do
  v0 <- evalToFO e0 env
  evalAltsU v0 alts
  where
    expStr = show (ECase e0 alts)

    evalAltsU v0 [] = throwError
      $ "Pattern match failure: "
      ++ show i
      ++ "\n"
      ++ show v0
      ++ " for "
      ++ expStr
    evalAltsU v0 ((p, g, e):alts)      -- FIXME
      = do
        res <- findMatchG p g v0 env
        case res of
          Nothing   -> evalAltsU v0 alts
          Just bind -> eval e (insertAll bind env)
eval_ info (ECaseB e0 alts) env = do
  start <- ask
  bx0 <- evalToBX e0 env
  -- trace (">>> " ++ show start ++ " " ++ show (ECaseB e0 alts)) $ return ()
  return
    $ VBX
      (evalAltsB start alts env expStr
       . pairL ("In case: " ++ showIE info e0) id bx0)
  where
    expStr = show (ECaseB e0 alts)

    evalAltsB :: Loc
              -> [(LPat, LGuard, Branch)]
              -> Env
              -> String
              -> Lens (Store, Value) Value
    evalAltsB start alts env msg = fromPartialGetPut get' put'
      where
        get' (store, v) = go alts
          where
            go :: [(LPat, LGuard, Branch)] -> Err Value
            go [] = rtError
              $ "Pattern match failure (in GET): "
              ++ show info
              ++ "\n"
              ++ show v
              ++ " for "
              ++ msg
            go ((p, g, Branch e cond _):alts)      -- FIXME
              = do
                res <- runE start (findMatchG p g v env)
                case res of
                  Nothing -> go alts
                  Just bind       -- trace (">> " ++ show (start, fromIntegral (length bind)) ++ " " ++ show bind ++ " " ++ show store) $
                    -> do
                      let next = start + fromIntegral (length bind)
                      let store' = foldr
                            (\((_, v), i) -> safeInsert "[case-get]" i v)
                            store
                            (zip bind [start ..])                       -- put方向には、xという名前は要らない。i -> vを入れる。下参照。
                      let env' = foldr
                            (\((x, v), i)
                             -> insert x (VBX $ lookupL' i)) -- つまり、x -> i を環境に入れている
                            (liftEnv start next env)
                            (zip bind [start ..])
                      lens <- runE next (evalToBX e env')
                      u <- get lens store'
                      runE start (checkAssert cond env u (show e))

        put' (store, orgSource) updView = do
          (pat, guard, Branch e cond recon, bind, ps)
            <- searchBranch orgSource updView alts
          let fvp = map fst bind
          let next = start + fromIntegral (length fvp)
          let store' =
                foldr (\((_, v), i) -> safeInsert "[case-puts]" i v) store
                $ zip bind [start ..]
          let env' = foldr
                (\(x, i) -> insert x (VBX $ lookupL' i))
                (liftEnv start next env)
                (zip fvp [start ..])
          lens <- runE next (evalToBX e env')
          store'' <- put lens store' updView
          let bind'' = foldr
                (\((x, org), i) -> case E.lookup i store'' of
                   Just upd -> ((x, upd):)
                   Nothing  -> trace
                     (show info
                      ++ "\n  "
                      ++ show x
                      ++ " is unused in: "
                      ++ show e
                      ++ ".\n  Used original value: "
                      ++ show org)
                     $ ((x, org):))
                []
                $ zip bind [start ..]
          let upd = unPat pat bind''
          guardCondResult <- runE start $ eval guard (insertAll bind'' env)
          isNoMatch <- checkNoMatch upd ps
          if isNoMatch && guardCondResult `equal` VTrue
            then return (foldr delete store'' [start .. next - 1], upd)
            else throwError
              $ show info ++ "\n  Branch condition fails for " ++ show upd
          where
            checkTrue :: LExp -> Value -> Err Bool
            checkTrue cond v = do
              r <- evalAsFOFunc start cond env v
              case r of
                VTrue -> return True
                _     -> return False

            searchBranch
              :: Value
              -> Value
              -> [(LPat, LGuard, Branch)]
              -> Err (LPat, LGuard, Branch, [(Name, Value)], [(LPat, LGuard)])
            searchBranch s v alts = do
              res1 <- goOrg alts []
              case res1 of
                Just br -> return br
                Nothing -> goFirstMatch alts []
              where
                -- res2 <- goFirstMatch alts []
                -- return $ fromJust $ res1 `mplus` return res2
                goOrg [] ps = return Nothing
                goOrg ((p, g, br@(Branch e cond r)):alts) ps = do
                  matchRes <- runE start $ findMatchG p g s env
                  case matchRes of
                    Just bind -> do
                      b <- checkTrue cond v
                      let trJust s = trace
                            ("Original branch is taken: "
                             ++ show info
                             ++ "\n  "
                             ++ show cond
                             ++ " becomes True for "
                             ++ show v)
                            (Just s)
                      return
                        $ if b
                          then trJust (p, g, br, bind, ps)
                          else Nothing
                    Nothing   -> goOrg alts ((p, g):ps)

                goFirstMatch [] ps = throwError
                  $ show info
                  ++ "\n  No with-conditions became True for "
                  ++ show v
                goFirstMatch ((p, g, br@(Branch e cond r)):alts) ps = do
                  isBranchCondTrue <- checkTrue cond v
                  if isBranchCondTrue
                    then do
                      bind <- doReconcile r s v p g
                      let trReturn s = return
                            $ trace
                              ("Branch switching happens: "
                               ++ show info
                               ++ "\n "
                               ++ show cond
                               ++ " becomes True for "
                               ++ show v)
                              s
                      trReturn (p, g, br, bind, ps)
                    else goFirstMatch alts ((p, g):ps)

                apply hp (VFun f) s = f hp s
                apply hp v s = throwError "Not a function"

                doReconcile e s v p g = do
                  newSource <- runE start
                    $ do
                      hp <- ask
                      f <- eval e env
                      g <- apply hp f s
                      apply hp g v
                  res <- runE start $ findMatchG p g newSource env
                  case res of
                    Just bind -> return bind
                    Nothing   -> throwError
                      $ "Patter match fails for reconciliation at "
                      ++ show (getLoc e)

            checkNoMatch :: Value -> [(LPat, LGuard)] -> Err Bool
            checkNoMatch upd [] = return True
            checkNoMatch upd ((p, g):ps) = do
              res <- runE start $ findMatchG p g upd env
              case res of
                Just _  -> return False
                Nothing -> checkNoMatch upd ps

        unPat :: LPat -> [(Name, Value)] -> Value
        unPat (unLoc -> PVar x) bind = case Prelude.lookup x bind of
          Just v  -> v
          Nothing -> rtError "Cannot happen"
        unPat (unLoc -> PNum n) bind = VNum n
        unPat (unLoc -> PChar c) bind = VChar c
        unPat (unLoc -> PCon n ps) bind = VCon n (map (\p -> unPat p bind) ps)
        unPat _ _ = rtError "Unreachable"

-- liftVal
liftVal :: HeapPointer -> HeapPointer -> Value -> Value
liftVal hpO hpN (VBX v) = VBX $ v . takeFirstN hpO hpN
liftVal hpO hpN (VFun f) = VFun $ \k -> f k
liftVal hpO hpN v = v

liftEnv :: HeapPointer -> HeapPointer -> Env -> Env
liftEnv hpO hpN env = vmap (liftVal hpO hpN) env

takeFirstN :: HeapPointer -> HeapPointer -> Lens Store Store
takeFirstN hpO hpN = fromGetPut get put
  where
    get :: Store -> Store
    get store   -- (\r -> trace (">>" ++ show store ++ " >> " ++ show r) r) $
      = foldr (\i -> delete i) store [hpO .. hpN - 1]

    put :: Store -> Store -> Store
    put store store' = store'

-- eval_ i (EAdd e1 e2) env = do
--   v1 <- eval e1 env
--   v2 <- eval e2 env
--   case (v1, v2) of
--     (VFO (VNum k1), VFO (VNum k2))
--       -> return $ VFO (VNum $ k1 + k2)
--     (VFO (VNum k), VBX bx)
--       -> return $ VBX (addL k . bx)
--     (VBX bx, VFO (VNum k))
--       -> return $ VBX (addL k . bx)
--     _ ->
--       err $ "Either first or second operand of + must be first-order value: "
--             ++ show v1 ++ ", " ++ show v2
--   where
--     addL k = fromInjection f g
--       where
--         f (Just (VNum n)) = Just $ VNum (n+k)
--         f (Just v)        = rtError $ "Not a number: " ++ show v
--         f Nothing         = Nothing
--         g (Just (VNum n)) = Just $ VNum (n-k)
--         g (Just v)        = rtError $ "Not a number: " ++ show v
--         g Nothing         = Nothing
-- eval_ i (EEq e1 e2) env = do
--   v1 <- eval e1 env
--   v2 <- eval e2 env
--   case (v1, v2) of
--     (VFO u1, VFO u2) ->
--       return $ VFO (if u1 == u2 then VTrue else VFalse)
--     (_, _) ->
--       err $ "Equivalence check can occur in FO expressions."
-- eval_ i (EAbort s) env =
--   err $ "Aborted: " ++ s
-- eval_ i (EDiscard x e1 e2) env = do
--   start <- ask
--   v1 <- eval e1 env
--   v2 <- local (+1) (eval e2 (insertE x (VBX $ lookupL start) env) >>= liftBX)
--   case (v1, v2) of
--     (VFO u, VBX bx) -> do
--       vx <- maybe (return Nothing) (fmap Just . liftBX) (lookupE x env)
--       case vx of
--         Just (VBX bx2) ->
--           return $ VBX (restoreL bx start u bx2)
--         Just v ->
--           return $ VBX bx
--         Nothing ->
--           err $ "Undefined variable: " ++ show x
--     _ ->
--       err $ "Default valuess must be first-order"
--   where
--     restoreL :: Lens Store (Maybe Value) -> Loc -> Value ->
--                 Lens Store (Maybe Value) -> Lens Store (Maybe Value)
--     restoreL bx start u bx2 = fromGetPut g p
--       where
--         g store   = do
--           u' <- get bx2 store
--           get bx (insertS start u' store)
--         p store v =
--           let store' = case get bx2 store of
--                 Just u' -> insertS start u' store
--                 Nothing -> insertS start u  store
--               store'' = put bx store' v
--               upd     = lookupS start store'' `mplus` lookupS start store' `mplus` Just u
--           in mergeStore (deleteS start store'') (put bx2 store upd)
-- eval_ i (ECon n es) env = do
--   vs <- mapM (\e -> eval e env) es
--   if allFO vs then
--     return $ VFO (VCon n [ v | VFO v <- vs ])
--   else do
--     bxs <- mapM (\v -> liftBX v >>= \(VBX bx) -> return bx) vs
--     return $ VBX $ conL n (length vs) . tupleL bxs
-- eval_ i (ENeg e) env = do
--   v <- eval e env
--   case v of
--     VFO (VNum k) -> return $ VFO (VNum (-k))
--     VBX bx       -> return $ VBX (negL . bx)
--     _ ->
--       err $ "Cannot negate non numbers."
--   where
--     negL = fromInjection neg neg
--     neg (Just (VNum n)) = Just (VNum (-n))
--     neg (Just v)        = rtError $ "Not a number: " ++ show v
--     neg Nothing         = Nothing
-- eval_ i (EBApp _ _) env = err "Not implemented yet."
class FV e where
  fv :: e -> [Name]

instance FV Pat where
  fv p = go p []
    where
      go (PVar x) r = x:r
      go (PCon n ps) r = foldr (\p -> go $ unLoc p) r ps
      go _ r = r

instance FV LPat where
  fv p = fv (unLoc p)

evalAsUsual :: LExp -> Env -> Err Value
evalAsUsual e env = runE initLoc $ eval e env

evalAsFOFunc :: HeapPointer -> LExp -> Env -> Value -> Err Value
evalAsFOFunc hp e env v = runE hp
  $ do
    res <- eval e env
    case res of
      VFun f -> f hp v
      _      -> throwError $ "Not a function: " ++ showEV e res

evalAsLens :: LExp -> Env -> Err (Lens Value Value)
evalAsLens e@(L i _) env = do
  let startLoc = mkLoc (-1)
  let x = NameI (-1)
  let env' = insert x (VBX $ lookupL' startLoc) env
  let exp = L noSrcSpan $ EApp e (L noSrcSpan $ EVar x)
  lens_ <- runE initLoc (evalToBX exp env')
  let lens = lens_ . storeL startLoc
  return lens -- fromGetPut (mkGet $ get lens) (mkPut $ put lens)
  where
    storeL :: Loc -> Lens Value Store
    storeL k = fromGetPut g p
      where
        g :: Value -> Store
        g v = insert k v empty

        p :: Value -> Store -> Value
        p o s = case E.lookup k s of
          Just s' -> s'
          Nothing -> o

    -- mkGet g v = fromJust $ g v
    --
    -- mkPut p a b = p a (Just b)
checkAssert :: LExp -> Env -> Value -> String -> E Value
checkAssert cond env v msg = do
  hp <- ask
  v0 <- eval cond env
  res <- case v0 of
    VFun f -> f hp v
    v      -> throwError $ "Not a function: " ++ showEV cond v
  case res of
    VTrue -> return v
    _     -> throwError
      $ "Assertion failed: `" ++ show v ++ "' is obtained.\n" ++ msg

findMatchG :: LPat -> LGuard -> Value -> Env -> E (Maybe [(Name, Value)])
findMatchG pat guard value env = do
  hp <- ask
  case findMatch pat value of
    Nothing   -> return Nothing
    Just bind -> do
      v <- eval guard (insertAll bind env)
      case v of
        VTrue  -> return (Just bind)
        VFalse -> return Nothing
        _      -> throwError
          $ show (getLoc guard)
          ++ ": Non Bool value in pattern guard"
          ++ show v

findMatch :: LPat -> Value -> Maybe [(Name, Value)]
findMatch (unLoc -> PCon n ps) (VCon m vs)
  | n == m && length ps == length vs = do
    res <- zipWithM findMatch ps vs
    return $ concat res
findMatch (unLoc -> PNum k) (VNum k')
  | k == k' = return []
findMatch (unLoc -> PChar c) (VChar c')
  | c == c' = return []
findMatch (unLoc -> PVar x) v = return [(x, v)]
findMatch _ _ = mzero

showEV :: LExp -> Value -> String
showEV e v = show e ++ " --> " ++ show v

showIE i e = show i ++ "\nNear: " ++ show e
-- liftMissing :: Lens a b -> Lens (Maybe a) (Maybe b)
-- liftMissing lens = fromGetPut g p
--   where
--     g = fmap   (get lens)
--     p = liftM2 (put lens)
