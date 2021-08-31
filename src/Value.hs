{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Value where

import           Control.DeepSeq (NFData(..))
import           Text.PrettyPrint as T hiding ((<>), Mode(..), empty)
import           Text.PrettyPrint.HughesPJClass as T hiding ((<>), Mode(..)
                                                           , empty)
import qualified Data.Map as M
import qualified Control.Monad.State as State
import           Control.Monad (unless)
import           Control.Monad.Except (throwError)
import           RunTimeException
import           Loc
import           Name
import           Util
import           Lens
import           E
import           Err
import           EnvLike

type HeapPointer = Loc

data Value = VCon Name [Value]
           | VNum Integer
           | VChar Char
           | VBX (Lens Store Value)
           | VFun (HeapPointer -> Value -> E Value)

isFO :: Value -> Bool
isFO (VBX _) = False
isFO (VFun _) = False
isFO _ = True

equal :: Value -> Value -> Bool
equal v1 v2
  | not (isFO v1) || not (isFO v2) =
    rtError "Equality is defined only for FO values."
equal (VCon n vs) (VCon m vs') = n == m && and (zipWith equal vs vs')
equal (VChar c) (VChar c') = c == c'
equal (VNum i) (VNum i') = i == i'
equal _ _ = False

less :: Value -> Value -> Bool
less v1 v2
  | not (isFO v1) || not (isFO v2) =
    rtError "Equality is defined only for FO values."
less (VNum i) (VNum i') = i < i'
less _ _ = False

pattern VLeft v = VCon (CName "Left") [v]

pattern VRight v = VCon (CName "Right") [v]

pattern VTrue = VCon (CName "True") []

pattern VFalse = VCon (CName "False") []

pattern VJust v = VCon (CName "Just") [v]

pattern VNothing = VCon (CName "Nothing") []

pattern VTup vs = VCon NTup vs

instance NFData Value where
  rnf (VCon n vs) = rnf (n, vs)
  rnf (VNum i) = rnf i
  rnf (VChar c) = rnf c
  rnf (VFun f) = ()
  rnf (VBX l) = rnf l

instance Pretty Value where
  pPrintPrec verbosity k (VTup vs) =
    parens $ hsep $ punctuate comma $ map (pPrintPrec verbosity 0) vs
  pPrintPrec verbosity k (VCon NNil []) = text "[]"
  pPrintPrec verbosity k v
    | Just str <- isStringLike v = text (show str)
  pPrintPrec verbosity k v
    | Just ls <- isListLike v =
      brackets $ cat $ punctuate comma $ map (pPrintPrec verbosity 0) ls
  pPrintPrec verbosity k (VCon n []) = text (show n)
  pPrintPrec verbosity k (VCon n vs) = parensIf (k > precApp)
    $ hsep (pPrint n:map (pPrintPrec verbosity (precApp + 1)) vs)
  pPrintPrec verbosity k (VNum i) = text (show i)
  pPrintPrec verbosity k (VChar c) = text (show c)
  pPrintPrec verbosity k (VBX _) = text "<lens>"
  pPrintPrec verbosity k (VFun _) = text "<fun>"

isStringLike :: Value -> Maybe String
isStringLike (VCon NNil []) = return []
isStringLike (VCon NCons [VChar c, xs]) = do
  rs <- isStringLike xs
  return $ c:rs
isStringLike _ = Nothing

isListLike :: Value -> Maybe [Value]
isListLike (VCon NNil []) = return []
isListLike (VCon NCons [x, xs]) = do
  rs <- isListLike xs
  return $ x:rs
isListLike _ = Nothing

instance Show Value where
  show = prettyShow

  -- show (VCon name vs) =
  --   "(VCon " ++ show name ++ " " ++ concatMap show vs ++ ")"
  -- show (VNum i) = "(VNum " ++ show i ++ ")"
  -- show (VChar c) = "(VChar " ++ show c ++ ")"
--------------------
newtype Store = Store (M.Map Loc Value)
  deriving (Show, EnvLike Loc Value)

mergeStore :: String -> Store -> Store -> Store
mergeStore msg (Store s1) (Store s2) = Store $ M.unionWith f s1 s2
  where
    f a b = if a `equal` b
            then a
            else rtError
              $ "Merge failed: " ++ show a ++ " vs " ++ show b ++ "\n" ++ msg

mergeStoreM :: String -> Store -> Store -> Err Store
mergeStoreM msg (Store s1) (Store s2) = Store
  <$> State.execStateT
    (M.traverseWithKey
       (\k v -> do
          m <- State.get
          case M.lookup k m of
            Nothing -> State.put $ M.insert k v m
            Just v' -> unless (v `equal` v')
              $ throwError
              $ "Merge failed: " ++ show v ++ " vs " ++ show v' ++ "\n" ++ msg)
       s1)
    s2
