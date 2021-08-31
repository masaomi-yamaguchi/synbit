module Command where

import Control.Arrow (first)
import Data.Function (on)
import Data.List (groupBy, sortBy)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Char (isSpace)

type CommandName = String

data CommandSpec a
  = NoArgCommand   CommandName a                     String
  | StringCommand  CommandName (String -> a)  String String

data CommandTrie a
  = Exec   String (String -> a) -- regidual string
  | Choice (M.Map Char (CommandTrie a))

instance Show (CommandTrie a) where
  show = go 0
    where
      go i (Exec s k) =
        replicate i ' ' ++ s ++ " -> <<cont>>\n"
      go i (Choice mp) =
        foldr (\(k,v) r ->
                replicate i ' ' ++ show k ++ " ->\n" ++
                go (i+4) v ++ r)
        []
        (M.toList mp)

commandUsage :: [CommandSpec a] -> String
commandUsage spec = go spec ""
  where
    go [] r = r
    go (NoArgCommand n _ d:ds) r =
      n ++ " \n" ++ "    " ++ d ++ "\n" ++ go ds r
    go (StringCommand n _ a d:ds) r =
      n ++ " " ++ a ++ " \n" ++ "    " ++ d ++ "\n" ++ go ds r


parseCommand :: [CommandSpec a] -> (String -> a) -> String -> a
parseCommand spec = \k str ->
  fromMaybe (k str) $ go trie str
  where
    trie = makeTrie spec
    go (Exec [] f)           str                 = return $ f str
    go (Exec residual f)     []                  = return $ f []
    go (Exec (r:residual) f) (s:str) | s == r    = go (Exec residual f) str
    go (Exec residual f)     (c:str) | isSpace c = return $ f str
    go (Exec (r:residual) f) (s:str)             = Nothing
    go (Choice mp) (s:str) =
      case M.lookup s mp of
        Just tr -> go tr str
        Nothing -> Nothing
    go t s = Nothing 

    makeTrie spec = h (g $ sortBy (compare `on` fst) $ map normalize spec)
      where
        g = groupBy ((==) `on` (head' . fst))
          where
            head' []     = Nothing
            head' (x:xs) = Just x
        normalize (NoArgCommand  s k _  ) = (s, const k)
        normalize (StringCommand s k _ _) = (s, k)

        h [[(s,k)]] = Exec s k
        h xss       =
          Choice $ M.fromList $
          map (\xs@((a:_,_):_) -> (a, h (g $ map (first tail) xs))) xss
