module DataDecl where

import           Prelude as P
import           Name
import qualified Syntax.Type as T

data DataDecl = TyData TName [T.TyVar] [(Name, [T.Ty])]

data DataDecl1 =
  TyData1 TName [T.TyVar] (Name, [T.Ty]) -- lookupTyの戻り値用

type DataEnv = [DataDecl]

instance Show DataDecl where
  show (TyData name vars consts) = "data "
    ++ show name
    ++ " "
    ++ concatMap (\a -> show a ++ " ") vars
    ++ "="
    ++ "\n"
    ++ concatMap
      (\(name, tys) -> show name
       ++ " "
       ++ concatMap (\ty -> "(" ++ show ty ++ ") ") tys
       ++ "\n")
      consts

defaultDataEnv :: DataEnv
defaultDataEnv =
  [ TyData (TName "Bool") [] [(NTrue, []), (NFalse, [])]
  , TyData
      (TName "[]")
      [T.BoundTv (Name "a")]
      [ (NNil, [])
      , ( NCons
        , [ T.TyVar (T.BoundTv (Name "a"))
          , T.TyApp (TName "[]") [T.TyVar (T.BoundTv (Name "a"))]])]]

addDataEnv :: DataEnv -> [T.TyDecl] -> DataEnv
addDataEnv = foldr
  (\decl env -> case decl of
     T.TyData name vars consts -> TyData name vars consts:env
     T.TyType {} -> env)

lookup :: TName -> DataEnv -> Maybe DataDecl
lookup _ [] = Nothing
lookup name ((TyData n vars decs):rest) =
  if name == n
  then Just (TyData n vars decs)
  else DataDecl.lookup name rest

lookupTy :: Name -> DataEnv -> Maybe DataDecl1
lookupTy _ [] = Nothing
lookupTy name ((TyData n vars decs):rest) = case P.lookup name decs of
  Nothing  -> lookupTy name rest
  Just tys -> Just (TyData1 n vars (name, tys))

contains :: DataEnv -> Name -> Bool
contains [] name = False
contains ((TyData _ _ consts):rest) name = any (\(n, _) -> n == name) consts
  || contains rest name
