-- | Abstract addresses
module Loc where


newtype Loc = Loc Int 
            deriving (Eq, Ord)

instance Enum Loc where
  toEnum           = Loc
  fromEnum (Loc i) = i

instance Num Loc where
  Loc i + Loc j = Loc (i+j) -- Only for +
  Loc i - Loc j = Loc (i-j)
  Loc i * Loc j = error "No multiplication for Loc"
  negate (Loc i) = error "No negation for Loc"
  abs    (Loc i) = Loc (abs i)
  signum (Loc i) = Loc (signum i)
  fromInteger n  = Loc (fromInteger n)
  

initLoc :: Loc
initLoc = mkLoc 0 
  

mkLoc :: Int -> Loc
mkLoc = Loc 

instance Show Loc where
  show (Loc i) = "@" ++ show i 
                     
