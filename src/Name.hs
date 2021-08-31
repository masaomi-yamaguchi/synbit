{-# LANGUAGE PatternSynonyms #-}

module Name where

import           Control.DeepSeq (NFData(..))
import           Text.PrettyPrint as T hiding ((<>), Mode(..))
import           Text.PrettyPrint.HughesPJClass as T hiding ((<>), Mode(..))

newtype TName = TName String
  deriving (Eq, Ord)

instance NFData TName where
  rnf (TName a) = rnf a

instance Pretty TName where
  pPrint (TName n) = text n

instance Show TName where
  show = prettyShow

data Name = SName Int -- Synthesisに使うuniqなname
          | Name String
          | CName String -- コンストラクタのname
          | NameI Int
          | Wrap1 Name -- GenExpのinstantiateに使う
  deriving (Eq, Ord)

instance Show Name where
  show = prettyShow

pattern NWild = Name "_"

pattern NCons = CName ":"

pattern NNil = CName "[]"

pattern NTup = CName ","

pattern NTrue = CName "True"

pattern NFalse = CName "False"

instance NFData Name where
  rnf (CName s) = rnf s
  rnf (Name s) = rnf s
  rnf (NameI i) = rnf i
  rnf (SName i) = rnf i

instance Pretty Name where
  pPrint NCons = text "(:)"
  pPrint NNil = text "[]"
  pPrint NTup = text "(,..,)"
  pPrint (Name s) = text s
  pPrint (NameI i) = text $ "$" ++ show i
  pPrint (SName i) = text $ "$x" ++ show i
  pPrint (CName c) = text c
