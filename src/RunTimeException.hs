module RunTimeException where

import Control.Exception (Exception, throw) 
import Data.Typeable (Typeable) 


data RunTimeException = RunTimeException String
  deriving Typeable

instance Show RunTimeException where
  show (RunTimeException str) = "Runtime Error: " ++ str

instance Exception RunTimeException

rtError :: String -> a
rtError str = throw (RunTimeException str)
