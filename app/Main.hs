module Main where

import           REPL
import           System.Console.GetOpt (getOpt, usageInfo, ArgDescr(OptArg)
                                      , ArgOrder(Permute), OptDescr(..))
import           System.Environment
import           Err
import           Syntax
import           Typing

options :: [OptDescr Int]
options = [ Option
              ['v']
              ["verbose"]
              (OptArg
                 (\s -> let r = maybe 1 (\s -> max (read s :: Int) 0) s
                        in r)
                 "INT")
              "Verbosity level [default = 1]"]

procOpts :: [String] -> (Int, Maybe FilePath)
procOpts argv = case getOpt Permute options argv of
  (o, n, [])   -> (last (1:o), foldr (const . Just) Nothing n)
  (_, _, errs) -> error (concat errs ++ usageInfo header options)
  where
    header = "Usage: HiBX [OPTION...] file"

main = do
  args <- getArgs
  uncurry startREPL (procOpts args)
  return ()
  where
    showDecl (Decl name mayBePolyTy e) = do
      print e
      print name
      print mayBePolyTy
      let tenv = defaultTyEnv
      let syn = defaultSynonyms
      let verb = 1
      res <- inferExp e (tenv, syn)
      case res of
        Bad s -> putStrLn s
        Ok t  -> print t

    showDecls [] = return ()
    showDecls (x:xs) = do
      showDecl x
      putStrLn ""
      showDecls xs
