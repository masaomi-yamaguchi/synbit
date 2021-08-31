module E where

import           Control.Monad.Reader (ReaderT, runReaderT)
import           Loc
import           Err

type E a = ReaderT Loc Err a

runE :: Loc -> E a -> Err a
runE loc x = runReaderT x loc
