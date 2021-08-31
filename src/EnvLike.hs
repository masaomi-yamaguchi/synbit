{-# LANGUAGE FunctionalDependencies, FlexibleInstances #-}

module EnvLike
  ( EnvLike(..)
  , pprEnvLike
  , showEnvLike
  )
where

import           Control.Arrow                  ( second )
import qualified Data.Map                      as M
import           Text.PrettyPrint.HughesPJ
import           Text.PrettyPrint.HughesPJClass

class EnvLike k v env | env -> v, env -> k where
  empty :: env
  insert :: k -> v -> env -> env

  singleton :: k -> v -> env
  singleton k v = insert k v EnvLike.empty

  insertAll :: EnvLike k v env' => env' -> env -> env
  insertAll xs e = foldr (uncurry insert) e $ toList xs

  fromEnvLike :: EnvLike k v env' => env' -> env
  fromEnvLike xs = insertAll xs EnvLike.empty

  delete :: k -> env -> env

  deleteAll :: [k] -> env -> env
  deleteAll ks e = foldr delete e ks

  lookup :: k -> env -> Maybe v

  toList :: env -> [(k,v)]
  fromList :: [(k,v)] -> env
  fromList = foldr (uncurry insert) EnvLike.empty

  vmap :: (v -> v) -> env -> env

  keys :: env -> [k]
  keys = map fst . toList

  values :: env -> [v]
  values = map snd . toList


instance Eq k => EnvLike k v [(k,v)] where
  empty = []
  insert k v = ((k, v) :)

  delete k [] = []
  delete k ((k', v) : r) | k == k'   = delete k r
                         | otherwise = (k', v) : delete k r

  toList = id
  vmap f = map (second f)

  lookup = Prelude.lookup

instance Ord k => EnvLike k v (M.Map k v) where
  empty  = M.empty
  insert = M.insert

  delete = M.delete

  toList = M.toList
  vmap   = M.map

  lookup = M.lookup

pprEnvLike :: (EnvLike k v e, Show k, Pretty v) => e -> Doc
pprEnvLike e = vcat $ map (\(k, v) -> hsep [text (showKey k), pPrint v]) kvs
 where
  kvs          = toList e
  maxKeyLength = foldr (max . length . show . fst) 0 kvs
  showKey k = take (maxKeyLength + 1) $ show k ++ ":" ++ repeat ' '

showEnvLike :: (EnvLike k v e, Show k, Show v) => e -> String
showEnvLike e = unlines $ map (\(k, v) -> showKey k ++ " " ++ show v) kvs
 where
  kvs          = toList e
  maxKeyLength = foldr (max . length . show . fst) 0 kvs
  showKey k = take (maxKeyLength + 1) $ show k ++ ":" ++ repeat ' '
