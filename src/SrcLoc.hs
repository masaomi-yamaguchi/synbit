{-# LANGUAGE CPP #-}

module SrcLoc where

import           Control.DeepSeq
import           Data.Monoid
import           Text.PrettyPrint               as T hiding ((<>))
import           Text.PrettyPrint.HughesPJClass as T hiding ((<>))

-- For compatiblity issue
import           Data.Semigroup                 as SG

data SrcLoc = SrcLoc { srcLocFile :: FilePath
                     , srcLocLine :: !Int
                     , srcLocCol  :: !Int }
            | NoSrcLoc String
            deriving (Eq, Show)

data SrcSpan
  = SrcSpan { srcSpanFile      :: FilePath,
              srcSpanStartLine :: !Int,
              srcSpanEndLine   :: !Int,
              srcSpanStarCol   :: !Int,
              srcSpanEndCol    :: !Int }
  | NoSrcSpan String
  deriving (Eq)


instance Show SrcSpan where
  show (NoSrcSpan s) = s
  show (SrcSpan fp sl el sc ec)
    | sl == el && sc == ec = "<" ++ fp ++ ":" ++ show sl ++ ":" ++ show sc ++ ">"
    | sl == el && sc /= ec = "<" ++ fp ++ ":" ++ show sl ++ ":" ++ show sc ++ "-" ++ show ec ++ ">"
    | sl /= el             = "<" ++ fp ++ ":" ++ "(" ++ show sl ++ ":" ++ show sc ++ ")-(" ++ show el ++ ":" ++ show ec ++ ")>"





data Located a = L SrcSpan a

unLoc :: Located a -> a
unLoc (L _ a) = a

getLoc :: Located a -> SrcSpan
getLoc (L s _) = s

noLoc :: a -> Located a
noLoc a = L noSrcSpan a

instance Functor Located where
  fmap f (L s a) = L s (f a)

instance Pretty a => Pretty (Located a) where
  pPrintPrec v k (L _ a) = pPrintPrec v k a

instance Pretty a => Show (Located a) where
  show = prettyShow

instance NFData a => NFData (Located a) where
  rnf (L loc a) = rnf (loc, rnf a)

instance NFData SrcSpan where
  rnf (NoSrcSpan s)        = rnf s
  rnf (SrcSpan fp _ _ _ _) = rnf fp

instance NFData SrcLoc where
  rnf (NoSrcLoc s)    = rnf s
  rnf (SrcLoc fp _ _) = rnf fp


srcLocSpan :: SrcLoc -> SrcSpan
srcLocSpan (SrcLoc fp l c) = SrcSpan   fp l l c c
srcLocSpan (NoSrcLoc s)    = NoSrcSpan s

mkSrcSpan :: SrcLoc -> SrcLoc -> SrcSpan
mkSrcSpan (NoSrcLoc s) _                     = NoSrcSpan s
mkSrcSpan _ (NoSrcLoc s)                     = NoSrcSpan s
mkSrcSpan (SrcLoc fp l1 c1) (SrcLoc _ l2 c2) = SrcSpan fp l1 l2 c1 c2

srcLocStart :: SrcSpan -> SrcLoc
srcLocStart (NoSrcSpan s)        = NoSrcLoc s
srcLocStart (SrcSpan fp l _ c _) = SrcLoc fp l c

srcLocEnd :: SrcSpan -> SrcLoc
srcLocEnd (NoSrcSpan s)        = NoSrcLoc s
srcLocEnd (SrcSpan fp _ l _ c) = SrcLoc fp l c

combineSrcSpans :: SrcSpan -> SrcSpan -> SrcSpan
combineSrcSpans (NoSrcSpan s) r = r
combineSrcSpans l (NoSrcSpan s) = l
combineSrcSpans (SrcSpan fp ls1 le1 cs1 ce1) (SrcSpan _ ls2 le2 cs2 ce2) =
  SrcSpan fp ls' le' cs' ce'
  where
    (ls', cs') = min (ls1, cs1) (ls2, cs2)
    (le', ce') = max (le1, ce1) (le2, ce2)

instance SG.Semigroup SrcSpan where
  (<>) = combineSrcSpans

instance Monoid SrcSpan where
  mempty  = noSrcSpan

#if !(MIN_VERSION_base(4,11,0))
  mappend = combineSrcSpans
#endif

noSrcLoc :: SrcLoc
noSrcLoc  = NoSrcLoc "<no location>"

noSrcSpan :: SrcSpan
noSrcSpan = srcLocSpan noSrcLoc



