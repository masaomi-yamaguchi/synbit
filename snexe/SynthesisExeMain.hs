module Main where

import           SynthesisMainUtil
import           System.Environment
import           System.TimeIt
import           System.Directory (getCurrentDirectory)
import           System.FilePath ((</>), takeDirectory)

main = do
  args <- getArgs
  curDir <- getCurrentDirectory
  case args of
    []    -> putStrLn "Err: file name is not specified"
    _:_:_ -> putStrLn "Err: the number of file names must be one."
    [fp]  -> timeIt
      $ do
        putStrLn
          "*******************************************************************"
        synthesis fp
        putStrLn $ "Time for example \"" ++ curDir </> fp ++ "\""
        putStrLn
          "*******************************************************************"
