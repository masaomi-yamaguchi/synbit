module Main (main) where

import           SynthesisMainUtil
import qualified Criterion.Types as C
import           Criterion.Main
import           System.Environment (getArgs, withArgs)

-- To show the benchmark of append, run
--  stack bench --benchmark-arguments "paper_experiments/List/append/spec.hobit"
main :: IO ()
main = do
  args <- getArgs
  let specFile = head args
  withArgs (drop 1 args)
    $ defaultMainWith
      defaultConfig
      [bgroup "synthesis" [bench specFile $ nfIO (synthesis specFile)]]
