module Util where

import Text.PrettyPrint as T hiding ((<>))
import Text.PrettyPrint.HughesPJClass as T hiding ((<>))

precApp :: Num a => a 
precApp  = 9

precAbs :: Num a => a 
precAbs  = 0

precAdd :: Num a => a 
precAdd  = 6

precCons :: Num a => a 
precCons = 6

data Assoc = AssocLeft | AssocRight | NoAssoc 

ppOp v k k0 assoc n e1 e2 =
  parensIf (k > k0) $
  hsep [ pPrintPrec v (k0+i) e1, text n, pPrintPrec v (k0+j) e2 ]
  where
    (i,j) = case assoc of
      AssocLeft  -> (0, 1)
      AssocRight -> (1, 0)
      NoAssoc    -> (1, 1) 

parensIf :: Bool -> Doc -> Doc 
parensIf b d | b         = parens d
             | otherwise = d
