{-# LANGUAGE MultiParamTypeClasses #-}

module REPL where

import           Command
import           Control.Monad (ap, liftM, when)
import           Control.Monad.Sharing
import           Err
import           Eval
import           Name
import           Syntax
import           Syntax.Parser
import           EnvLike as E
import           Lens
import           RunTimeException
import           SrcLoc (noSrcSpan, unLoc, Located(L))
import           Syntax.Type as S
import           Syntax.Typed as TD
import           Synthesis.BxTyping as SB
import qualified Synthesis.BxFrame as SF
import           Typing
import           Value
import           Control.DeepSeq (NFData, deepseq)
import           Control.Exception (SomeException, catch, evaluate)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Control.Monad.State (MonadState)
import qualified Control.Monad.State as State (get, gets, modify, put)
import           Data.IORef
import           Data.List (isPrefixOf)
import qualified Data.Map as M
import           Debug.Trace
import qualified System.Console.Haskeline as HL
import           System.Directory (doesFileExist, getCurrentDirectory
                                 , getHomeDirectory)
import           System.FilePath ((</>))
import           System.IO (hFlush, stdout)
import           System.IO.Error (isEOFError)
import           Synthesis.LazyEvalG (getTest, getTraceTest)
import           Synthesis.LazyEvalP (putTest)
import           DataDecl
import           Synthesis.GenExp (genExpTest, genTypeTest)
import           Synthesis.SynthesisMain -- (fillHoleTest, synthesisTest, Example)

type VerbosityLevel = Int

data Conf =
  Conf { currentEnv :: Env
       , currentTyEnv :: TyEnv
       , currentTySyn :: Synonyms
       , currentFilePath :: Maybe FilePath
       , currentDir :: !FilePath
       , currentTExpEnv :: TExpEnv  -- Typingで定義
       , currentNonBXTExpEnv :: TExpEnv -- Synthesisで使える関数の集合
       , currentDataEnv :: DataEnv
       , currentExamples :: [Example]
       , verbosity :: !VerbosityLevel
       , uniqSupply :: IORef Int
       }

initConf :: IO Conf
initConf = do
  dir <- getCurrentDirectory
  ref <- newIORef 0
  return
    Conf { currentEnv = defaultEnv
         , currentTyEnv = defaultTyEnv
         , currentTySyn = defaultSynonyms
         , currentFilePath = Nothing
         , currentDir = dir
         , currentTExpEnv = defaultTExpEnv
         , currentNonBXTExpEnv = defaultTExpEnv
         , currentDataEnv = defaultDataEnv
         , currentExamples = []
         , verbosity = 1
         , uniqSupply = ref
         }

newtype REPL a = REPL { runREPL :: IORef Conf -> HL.InputT IO a }

instance Functor REPL where
  fmap = liftM

instance Applicative REPL where
  pure = return

  (<*>) = ap

instance Monad REPL where
  return x = REPL $ const (return x)

  REPL x >>= f = REPL
    $ \ref -> do
      v <- x ref
      runREPL (f v) ref

instance MonadState Conf REPL where
  get = REPL $ \ref -> liftIO $ readIORef ref

  put x = REPL $ \ref -> liftIO $ writeIORef ref x

instance MonadIO REPL where
  liftIO x = REPL $ const (liftIO x)

liftInput :: HL.InputT IO a -> REPL a
liftInput x = REPL $ const x

-- replaceComplete :: HL.CompletionFunc IO -> REPL ()
-- replaceComplete func = do
replCompletion :: IORef Conf -> HL.CompletionFunc IO
replCompletion ref (curr, rest) = case checkLoadMode curr of
  Just (prefix, sp, r) -> do
    (s, cs) <- HL.completeFilename (reverse r, rest)
    return (s ++ reverse (prefix ++ sp), cs)
  Nothing -> completeIDs (curr, rest)
  where
    completeIDs :: HL.CompletionFunc IO
    completeIDs (curr, rest) = HL.completeWord
      Nothing
      " \t\n\r"
      (\s -> do
         ids <- keys . currentTyEnv <$> readIORef ref
         return
           $ map HL.simpleCompletion
           $ filter (s `isPrefixOf`)
           $ [n | CName n <- ids] ++ [m | Name m <- ids] ++ commands curr)
      (curr, rest)
      where
        commands :: String -> [String]
        commands curr
          | not (any (`elem` " \t\r\n") curr)
            && not (null curr)
            && last curr == ':' = commandStrings
          | otherwise = []

        commandStrings :: [String]
        commandStrings = [s | NoArgCommand s _ _ <- commandSpec]
          ++ [s | StringCommand s _ _ _ <- commandSpec]

    -- checks if str is has the form "... DOAL"
    checkLoadMode :: String -> Maybe (String, String, String)
    checkLoadMode = check . parse . reverse
      where
        parse s = let (w1, rest) = break isSpace s
                      (s1, w2) = span isSpace rest
                  in (w1, s1, w2)

        isSpace = (`elem` " \t\r\n")

        check (w1, s1, w2)
          | isLoadPrefix w1 && not (null s1) = Just (w1, s1, w2)
          | otherwise = Nothing

        isLoadPrefix [] = False
        isLoadPrefix [_] = False
        isLoadPrefix str = str `isPrefixOf` ":load"

startREPL :: VerbosityLevel -> Maybe FilePath -> IO ()
startREPL v z = do
  conf <- initConf
  let conf' = conf { verbosity = v }
  ref <- newIORef conf'
  let setting = HL.setComplete (replCompletion ref) HL.defaultSettings
  homeDir <- getHomeDirectory
  let histfilepath = homeDir </> ".HOBiT_history"
  let setting' = setting { HL.historyFile = Just histfilepath }
  case z of
    Nothing -> HL.runInputT setting' $ runREPL askCommand ref
    Just fp -> HL.runInputT setting' $ runREPL (procLoad fp) ref

commandSpec :: [CommandSpec (REPL ())]
commandSpec =
  [ NoArgCommand ":quit" (return ()) "Quit REPL."
  , StringCommand ":load" procLoad "FILEPATH" "Load a program."
  , NoArgCommand ":reload" procReload "Reload the last program."
  , StringCommand
      ":put"
      procPut
      "EXP [EXP [EXP]]"
      "Evaluate a function as \"put\"."
  , StringCommand ":get" procGet "Exp [Exp]" "Evaluate a function as \"get\"."
  , StringCommand
      ":set verbosity"
      procSetVerbosity
      "INT"
      "Set verbosity to the specified number."
  , NoArgCommand ":help" procHelp "Show this help."
  , StringCommand ":synthesis" procSynthesis "NAME" "Synthesis"
  , StringCommand
      ":fill"
      procFillHoles
      "NAME"
      "Synthesis frames and fill holes"
  , StringCommand ":frameall" procFrameAll "NAME" "Synthesis frames"
  , StringCommand ":td" procTyped "FILEPATH" "Convert program into typed one."
  , StringCommand
      ":snload"
      procLoadSynthesis
      "FILEPATH"
      "Convert program into typed one for synthesis."
  , StringCommand ":exload" procLoadExamples "FILEPATH" "load examples"
  , StringCommand
      ":bxtype"
      procBxType
      "EXP"
      "Convert expression's type into BX and Show them."
  , StringCommand
      ":bxframe"
      procBxFrame
      "NAME"
      "Convert expression into BX one and Show them."
  , StringCommand
      ":lazyGet"
      procLazyGet
      "Name"
      "Eval in the get direction lazily."
  , StringCommand
      ":lazyPut"
      procLazyPut
      "Name"
      "Eval in the put direction lazily."
  , StringCommand
      ":lazyTrace"
      procLazyGetTrace
      "Name"
      "Eval in the get direction lazily."
  , StringCommand ":genExp" procGenExp "Name" "Genarate well-typed expression"
    -- , StringCommand ":gen3" procGenExp3 "Name" "Genarate well-typed expression"
  , NoArgCommand ":genType" procGenType "Generate types"
  , StringCommand ":type" procType "EXP" "Show expression's type."]

procSetVerbosity :: String -> REPL ()
procSetVerbosity str = do
  let i = max (read str :: Int) 0
  liftIO $ putStrLn $ "Verbosity is set to: " ++ show i
  i `seq` State.modify (\conf -> conf { verbosity = i })
  askCommand

  -- catchAny
  --   (do putStrLn $ "Verbosity is set to: " ++ show i
  --       local (\conf -> conf { verbosity = i }) askCommand)
  --   (\_ -> askCommand)
procLoad :: String -> REPL ()
procLoad filepath = do
  v <- State.gets verbosity
  loadProgram
    v
    (trimSpace filepath)
    (State.modify (\conf -> conf { currentFilePath = Just filepath })
     >> askCommand)
    $ \env' tenv' syn' -> State.modify
      (\conf -> conf { currentEnv = env'
                     , currentTyEnv = tenv'
                     , currentTySyn = syn'
                     , currentFilePath = Just filepath
                     })
    >> askCommand

trimSpace string = case string of
  []      -> []
  (' ':s) -> trimSpace s
  ('"':s) -> findDQ s
  ss      -> trimTraingSpace ss
  where
    trimTraingSpace = reverse . dropWhile (== ' ') . reverse

    findDQ [] = rtError "No matching quote"
    findDQ ('"':s) = []
    findDQ (c:s) = c:findDQ s

procReload :: REPL ()
procReload = do
  maybeFile <- State.gets currentFilePath
  case maybeFile of
    Just fp -> procLoad fp
    Nothing -> do
      liftIO $ putStrLn "No file has been loaded."
      askCommand

loadProgram :: Int
            -> FilePath
            -> REPL ()
            -> (Env -> TyEnv -> Synonyms -> REPL ())
            -> REPL ()
loadProgram vlevel fp kfail ksucc = do
  curDir <- State.gets currentDir
  r <- liftIO
    $ catchAny
      (go curDir fp [] defaultEnv defaultTyEnv defaultSynonyms)
      (\e -> print e >> return Nothing)
  case r of
    Just (env, tenv, syn) -> liftIO (putStrLn "Ok.") >> ksucc env tenv syn
    Nothing -> liftIO (putStrLn "Error(s) occurred.") >> kfail
  where
    go curDir fp proced env tenv syn
      | fp `elem` proced = return $ Just (env, tenv, syn)
    go curDir fp proced env tenv syn = do
      str <- readFile (curDir </> fp)
      case parseProgram fp str of
        Bad errs -> do
          putStrLn errs
          return Nothing
        Ok (fps, tdecls, prog) -> do
          let f [] pc env tenv syn = return $ Just (env, tenv, syn)
              f (fp:fps) pc env tenv syn = do
                r <- go curDir fp pc env tenv syn
                case r of
                  Just (env', tenv', syn') -> f fps (fp:pc) env' tenv' syn'
                  Nothing -> return Nothing
          r <- f fps proced env tenv syn
          case r of
            Nothing -> return Nothing
            Just (env', tenv', syn') -> do
              when (vlevel > 1)
                $ do
                  putStrLn "Desugared program:"
                  print (map unLoc prog)
              let (tenv'', syn'') = toTyEnv (tenv', syn') tdecls
              res <- inferDecls prog (tenv'', syn'')
              case res of
                Bad errs   -> do
                  putStrLn errs
                  return Nothing
                Ok tenv''' -> do
                  putStrLn $ "* Loaded Symbols from <" ++ fp ++ ">"
                  let forPrint = foldr
                        (\(L _ (Decl n _ _))
                         -> maybe id (E.insert n) (E.lookup n tenv'''))
                        E.empty
                        prog :: TyEnv
                  print forPrint
                  return (Just (toEnv env' prog, tenv''', syn''))

procHelp :: REPL ()
procHelp = do
  liftIO $ putStr $ commandUsage commandSpec
  askCommand

procGet :: String -> REPL ()
procGet str = case parseGetArg str of
  Bad errs  -> do
    liftIO $ putStrLn errs
    askCommand
  Ok (e:es) -> do
    checkType e lType
      $ evalAndCheckLens e
      $ \lens _ -> do
        (sourceExp, es') <- nextExpression "source = " es
        checkType (eTup [e, sourceExp]) lsType
          $ evalAndCheck sourceExp
          $ \src _ -> runErr (get lens src) $ \view -> liftIO $ print view
    askCommand

eTup = L noSrcSpan . S.ECon False NTup

(lType, lsType, lsvType, lsvsType) =
  ( TyForAll [a, b] tl
  , TyForAll [a, b] $ TyTup [tl, ta]
  , TyForAll [a, b] $ TyTup [tl, ta, tb]
  , TyForAll [a, b] $ TyTup [tl, ta, tb, ta])
  where
    tl = TyB ta `TyArr` TyB tb

    a = BoundTv (Name "a")

    b = BoundTv (Name "b")

    ta = TyVar a

    tb = TyVar b

procPut :: String -> REPL ()
procPut str = case parsePutArg str of
  Bad errs  -> do
    liftIO $ putStrLn errs
    askCommand
  Ok (e:es) -> do
    checkType e lType
      $ evalAndCheckLens e
      $ \lens tyLens -> do
        (sourceExp, es') <- nextExpression "source = " es
        checkType (eTup [e, sourceExp]) lsType
          $ evalAndCheck sourceExp
          $ \src _ -> runErr (get lens src)
          $ \oldView -> do
            liftIO $ putStrLn $ "Result of get: " ++ show oldView
            (viewExp, _) <- nextExpression "updated view = " es'
            checkType (eTup [e, sourceExp, viewExp]) lsvType
              $ evalAndCheck viewExp
              $ \updView _ -> runErr (put lens src updView) (liftIO . print)
    askCommand

nextExpression :: String -> [LExp] -> REPL (LExp, [LExp])
nextExpression str [] = do
  e <- askExp str
  return (e, [])
nextExpression str (e:es) = return (e, es)

procType :: String -> REPL ()
procType str = case parseExp str of
  Bad errs -> do
    liftIO $ putStrLn errs
    askCommand
  Ok e     -> do
    -- inferType :: LExp -> (Ty -> REPL ()) -> REPL ()
    inferType e (\t -> liftIO (print t))
    askCommand

procBxType :: String -> REPL ()
procBxType str = case parseExp str of
  Bad errs -> do
    liftIO $ putStrLn errs
    askCommand
  Ok e -> do
    inferType
      e
      (\ty -> do
          -- liftIO $ SN.printSM (SN.tyB ty) -- 旧バージョン
         tybxs <- liftIO $ resultListIO (SB.synthesisB pen ty >>= convert)
         liftIO $ printList (tybxs :: [Ty]))
    askCommand
    where
      pen = 100

procBxFrame :: String -> REPL ()
procBxFrame fname = do
  env <- State.gets currentTyEnv
  syn <- State.gets currentTySyn
  denv <- State.gets currentDataEnv
  liftIO $ putStrLn "Current Data Env ::"
  liftIO $ mapM_ print denv
  ref <- State.gets uniqSupply
  let f = Name (trimSpace fname)
  tdenv <- State.gets currentTExpEnv
  liftIO $ putStrLn "Current TExp Env ::"
  liftIO $ putStrLn $ showEnvLike tdenv
  case E.lookup f tdenv of
    Just e  -> liftIO
      $ do
        ret <- (SF.makeFramesTest env syn denv ref f e)
        printList ret
    Nothing -> liftIO $ putStrLn $ "We cannnot find " ++ show f
  askCommand

-- typedな項に変換してSynthesis用のEnvironmentに追加する
procTyped :: String -> REPL ()
procTyped filepath = do
  v <- State.gets verbosity
  loadProgram
    v
    (trimSpace filepath)
    (State.modify (\conf -> conf { currentFilePath = Just filepath })
     >> askCommand)
    $ \env' tenv' syn' -> State.modify
      (\conf -> conf { currentEnv = env'
                     , currentTyEnv = tenv'
                     , currentTySyn = syn'
                     , currentFilePath = Just filepath
                     })
  tenv <- State.gets currentTyEnv
  syn <- State.gets currentTySyn
  dir <- State.gets currentDir
  ref <- State.gets uniqSupply
  denv <- State.gets currentDataEnv
  let path = trimSpace dir ++ "/" ++ trimSpace filepath
  loaded <- liftIO $ loadDecls path
  case loaded of
    Bad s -> do
      liftIO $ putStrLn s
      liftIO $ putStrLn $ filepath ++ "cannnot load."
      askCommand
    Ok (tyDecls, decls) -> do
      State.modify (\conf -> conf { currentDataEnv = addDataEnv denv tyDecls })
      denv <- State.gets currentDataEnv
      liftIO $ mapM_ print denv
      mapM_
        (\(Decl name mty lexp) -> do
           errTExp <- liftIO
             $ inferDeclToTExp (Decl name mty lexp) (tenv, syn) ref
           case errTExp of
             Bad s   -> liftIO $ putStrLn s
             Ok texp -> do
               tdenv <- State.gets currentTExpEnv
               let tdenv' = insert name texp tdenv
               State.modify (\conf -> conf { currentTExpEnv = tdenv' })
               liftIO $ putStr $ show name ++ " = "
               liftIO $ putStrLn $ showTExp texp
               liftIO $ putStrLn "")
        decls
      askCommand

-- fixme
-- Typeを考えていない
procLoadExamples :: String -> REPL ()
procLoadExamples filepath = do
  env <- State.gets currentEnv
  dir <- State.gets currentDir
  let path = trimSpace dir ++ "/" ++ trimSpace filepath
  loaded <- liftIO $ loadDecls path
  case loaded of
    Bad s -> do
      liftIO $ putStrLn s
      liftIO $ putStrLn $ filepath ++ "cannnot load."
      askCommand
    Ok (tyDecls, decls) -> do
      mapM_
        (\(Decl name mty lexp) -> do
           case evalAsUsual lexp env of
             Bad s -> do
               liftIO $ putStrLn s
               liftIO $ putStrLn $ filepath ++ "cannnot load."
               askCommand
             Ok (VCon NTup [s, v, s']) -> do
               examples <- State.gets currentExamples
               State.modify
                 (\conf -> conf { currentExamples = (Example s undefined v s')
                                    :examples
                                })
             Ok _ -> do
               liftIO $ putStrLn $ filepath ++ "cannnot load."
               liftIO
                 $ putStrLn
                 $ "example " ++ show name ++ " is not a 3-tuple."
               askCommand)
        decls
      askCommand

procLoadSynthesis :: String -> REPL ()
procLoadSynthesis filepath = do
  v <- State.gets verbosity
  loadProgram
    v
    (trimSpace filepath)
    (State.modify (\conf -> conf { currentFilePath = Just filepath })
     >> askCommand)
    $ \env' tenv' syn' -> State.modify
      (\conf -> conf { currentEnv = env'
                     , currentTyEnv = tenv'
                     , currentTySyn = syn'
                     , currentFilePath = Just filepath
                     })
  tenv <- State.gets currentTyEnv
  env <- State.gets currentEnv
  syn <- State.gets currentTySyn
  dir <- State.gets currentDir
  ref <- State.gets uniqSupply
  denv <- State.gets currentDataEnv
  fs <- askNames "BX Funs: "
  let path = trimSpace dir ++ "/" ++ trimSpace filepath
  loaded <- liftIO $ loadDecls path
  case loaded of
    Bad s -> do
      liftIO $ putStrLn s
      liftIO $ putStrLn $ filepath ++ "cannnot load."
      askCommand
    Ok (tyDecls, decls) -> do
      State.modify (\conf -> conf { currentDataEnv = addDataEnv denv tyDecls })
      denv <- State.gets currentDataEnv
      -- liftIO $ putStrLn "Current Data Env ::"
      -- liftIO $ mapM_ print denv
      mapM_
        (\(Decl name mty lexp) -> do
           errTExp <- liftIO
             $ inferDeclToTExp (Decl name mty lexp) (tenv, syn) ref
           case errTExp of
             Bad s   -> liftIO $ putStrLn s
             Ok texp -> do
               if name `elem` fs
                 then do
                   tdenv <- State.gets currentTExpEnv
                   State.modify
                     (\conf -> conf { currentTExpEnv = insert name texp tdenv })
                 else do
                   tdenv <- State.gets currentNonBXTExpEnv
                   State.modify
                     (\conf
                      -> conf { currentNonBXTExpEnv = insert name texp tdenv })
               liftIO $ putStr $ show name ++ " = "
               liftIO $ putStrLn $ showTExp texp
               liftIO $ putStrLn "")
        decls
      -- State.modify
      --   (\conf -> conf { currentTyEnv = E.deleteAll fs tenv
      --                  , currentEnv = E.deleteAll fs env
      --                  })
      askCommand

procSynthesis :: String -> REPL ()
procSynthesis f0name = do
  let f0 = Name (trimSpace f0name)
  env <- State.gets currentNonBXTExpEnv
  tyenv <- State.gets currentTyEnv
  syn <- State.gets currentTySyn
  ref <- State.gets uniqSupply
  tdenv <- State.gets currentTExpEnv
  denv <- State.gets currentDataEnv
  examples <- State.gets currentExamples
  liftIO $ putStrLn "Current NonBX Env ::"
  liftIO $ putStrLn $ showEnvLike env
  liftIO $ putStrLn "Current TExp Env ::"
  liftIO $ putStrLn $ showEnvLike tdenv
  case E.lookup f0 tdenv of
    Just e  -> liftIO
      $ do
        let ret = synthesisMain
              tyenv
              syn
              denv
              ref
              (E.toList env)
              (f0, e)
              (E.toList $ E.delete f0 tdenv)
              examples
        putStrLn "\nresult:"
        print ret
    Nothing -> liftIO $ putStrLn $ "We cannnot find " ++ show f0
  askCommand

procFillHoles :: String -> REPL ()
procFillHoles f0name = do
  let f0 = Name (trimSpace f0name)
  env <- State.gets currentNonBXTExpEnv
  tyenv <- State.gets currentTyEnv
  syn <- State.gets currentTySyn
  ref <- State.gets uniqSupply
  tdenv <- State.gets currentTExpEnv
  denv <- State.gets currentDataEnv
  liftIO $ putStrLn "Current TExp Env ::"
  liftIO $ putStrLn $ showEnvLike tdenv
  n <- askNum "Num: "
  case E.lookup f0 tdenv of
    Just e  -> liftIO
      $ do
        ret <- fillHoleTest
          tyenv
          syn
          denv
          ref
          (E.toList env)
          (f0, e)
          (E.toList $ E.delete f0 tdenv)
        putStrLn "\nresult:"
        printList (take n ret)
    Nothing -> liftIO $ putStrLn $ "We cannnot find " ++ show f0
  askCommand

procFrameAll :: String -> REPL ()
procFrameAll f0name = do
  let f0 = Name (trimSpace f0name)
  env <- State.gets currentTyEnv
  syn <- State.gets currentTySyn
  ref <- State.gets uniqSupply
  tdenv <- State.gets currentTExpEnv
  denv <- State.gets currentDataEnv
  liftIO $ putStrLn "Current TExp Env ::"
  liftIO $ putStrLn $ showEnvLike tdenv
  case E.lookup f0 tdenv of
    Just e  -> liftIO
      $ do
        ret <- SF.makeFramesAllTest
          env
          syn
          denv
          ref
          (f0, e)
          (E.toList $ E.delete f0 tdenv)
        putStrLn "\nresult:"
        printList ret
        putStrLn $ "\n \n total candidates: " ++ show (length ret)
    Nothing -> liftIO $ putStrLn $ "We cannnot find " ++ show f0
  askCommand

procLazyGet :: String -> REPL ()
procLazyGet f_str = do
  let f = Name (trimSpace f_str)
  tdenv <- State.gets currentTExpEnv
  ev <- State.gets currentEnv
  s <- askExp "Source: "
  v <- liftIO $ getTest (E.toList tdenv) f s ev
  liftIO $ putStrLn $ "View: "
  liftIO $ printList v
  askCommand

procLazyPut :: String -> REPL ()
procLazyPut f_str = do
  let f = Name (trimSpace f_str)
  tdenv <- State.gets currentTExpEnv
  env <- State.gets currentEnv
  s <- askExp "Source : "
  v <- askExp "View   : "
  ss' <- liftIO $ putTest (E.toList tdenv) f s v env
  let [s'] = if length ss' == 1
             then map show ss'
             else ["procLazyPut: Execution Err. There is no solution."]
  liftIO $ putStrLn $ "Source': "
  liftIO $ putStrLn s'
  askCommand

procLazyGetTrace :: String -> REPL ()
procLazyGetTrace f_str = do
  let f = Name (trimSpace f_str)
  tdenv <- State.gets currentTExpEnv
  ev <- State.gets currentEnv
  s <- askExp "Source: "
  v <- liftIO $ getTraceTest (E.toList tdenv) f s ev
  liftIO $ putStrLn $ "View: "
  liftIO $ printList v
  askCommand

procGenExp :: String -> REPL ()
procGenExp str = case parseTy str of
  Bad errs -> do
    liftIO $ putStrLn errs
    askCommand
  Ok ty    -> do
    env <- State.gets currentTyEnv
    -- tdenv <- State.gets currentTExpEnv
    syn <- State.gets currentTySyn
    denv <- State.gets currentDataEnv
    ref <- State.gets uniqSupply
    -- inferType :: LExp -> (Ty -> REPL ()) -> REPL ()
    liftIO (print ty)
    n <- askNum "Num: "
    es <- liftIO $ genExpTest env syn denv ref ty
    liftIO $ printList (take n es)
    askCommand

-- procGenExp3 :: String -> REPL ()
-- procGenExp3 str = case parseTy str of
--   Bad errs -> do
--     liftIO $ putStrLn errs
--     askCommand
--   Ok ty    -> do
--     env <- State.gets currentTyEnv
--     -- tdenv <- State.gets currentTExpEnv
--     syn <- State.gets currentTySyn
--     denv <- State.gets currentDataEnv
--     ref <- State.gets uniqSupply
--     -- inferType :: LExp -> (Ty -> REPL ()) -> REPL ()
--     liftIO (print ty)
--     n <- askNum "Num: "
--     es <- liftIO $ genExpTest3 env syn denv ref ty
--     liftIO $ printList (take n es)
--     askCommand
procGenType :: REPL ()
procGenType = do
  env <- State.gets currentTyEnv
  -- tdenv <- State.gets currentTExpEnv
  syn <- State.gets currentTySyn
  denv <- State.gets currentDataEnv
  ref <- State.gets uniqSupply
  -- inferType :: LExp -> (Ty -> REPL ()) -> REPL ()
  n <- askNum "Num: "
  es <- liftIO $ genTypeTest env syn denv ref
  liftIO $ printList (take n es)
  askCommand

loadDecls :: FilePath -> IO (Err ([TyDecl], [Decl]))
loadDecls fp = do
  str <- readFile fp
  case parseProgram fp str of
    Bad errs -> return $ Bad errs
    Ok (fps, tyDecls, lDecls) -> case map unLoc lDecls of
      []    -> return $ Bad "No Input."
      decls -> return $ Ok (tyDecls, decls)

evalAndCheck :: LExp -> (Value -> Ty -> REPL ()) -> REPL ()
evalAndCheck e k = inferType e
  $ \t -> do
    env <- State.gets currentEnv
    runErr (evalAsUsual e env) (\x -> k x t)

evalAndCheckLens :: LExp -> (Lens Value Value -> Ty -> REPL ()) -> REPL ()
evalAndCheckLens e k = inferType e
  $ \t -> do
    env <- State.gets currentEnv
    runErr (evalAsLens e env) (\x -> k x t)

inferType :: LExp -> (Ty -> REPL ()) -> REPL ()
inferType e k = do
  tenv <- State.gets currentTyEnv
  syn <- State.gets currentTySyn
  verb <- State.gets verbosity
  res <- liftIO $ inferExp e (tenv, syn)
  case res of
    Bad s -> liftIO $ putStrLn s
    Ok t  -> do
      liftIO $ when (verb > 2) $ reportExpAndType e t
      k t

checkType :: LExp -> Ty -> REPL () -> REPL ()
checkType e t k = do
  tenv <- State.gets currentTyEnv
  verb <- State.gets verbosity
  syn <- State.gets currentTySyn
  res <- liftIO $ checkExp e (tenv, syn) t
  case res of
    Bad s -> liftIO (putStrLn s)
    Ok () -> k

reportExpAndType :: LExp -> Ty -> IO ()
reportExpAndType e t = do
  putStrLn $ take 80 $ "--- desugared expression ---" ++ repeat '-'
  print e
  putStrLn $ " :: " ++ show t
  putStrLn $ replicate 80 '-'

procExp :: String -> REPL ()
procExp "" = askCommand
procExp str = case parseExp str of
  Bad errs -> do
    liftIO $ putStrLn errs
    askCommand
  Ok e     -> do
    evalAndCheck e
      $ \res _ -> case res of
        VBX l -> do
          liftIO $ putStrLn "<lens>"
          runErr (get l empty)
            $ \getresult -> do
              liftIO $ putStr "get result: "
              liftIO $ print getresult
        _     -> liftIO $ print res
    askCommand

askCommand :: REPL ()
askCommand = do
  maybeLine <- liftInput $ HL.getInputLine "HOBiT> "
  case maybeLine of
    Nothing -> do
      liftIO $ putStrLn "Quiting ..."
      return ()
    Just s  -> parseCommand commandSpec procExp s

  -- withLine (\e -> if isEOFError e then return () else print e >> askCommand conf) $ \s ->
  --   if null s then askCommand conf
  --   else parseCommand commandSpec procExp s conf
-- withLine :: (IOError -> IO a) -> (String -> IO a)-> IO a
-- withLine handler k =
--   catch (getLine >>= k)
--   (\e -> let _ = e :: IOError
--          in handler e)
runErr :: NFData a => Err a -> (a -> REPL ()) -> REPL ()
runErr r k1 = do
  maybeX <- liftIO
    $ catchRunTimeError
      (do
         x <- evaluate (runErr' r)
         deepseq x (return $ Just x))
      (\e -> catchAny
         (print e)
         (\e -> putStrLn "LoL: print throws an error" >> print e)
       >> return Nothing)
  maybe (return ()) k1 maybeX
  where
    runErr' (Ok x) = x
    runErr' (Bad s) = rtError s

catchRunTimeError :: IO a -> (RunTimeException -> IO a) -> IO a
catchRunTimeError = catch

catchAny :: IO a -> (SomeException -> IO a) -> IO a
catchAny = catch

askExp :: String -> REPL LExp
askExp prompt = do
  maybeLine <- liftInput $ HL.getInputLine prompt
  case maybeLine of
    Nothing -> askExp prompt
    Just s  -> case parseExp s of
      Bad errs -> do
        liftIO $ putStrLn $ "Error: " ++ errs
        askExp prompt
      Ok e     -> return e

askName :: String -> REPL Name
askName prompt = do
  maybeLine <- liftInput $ HL.getInputLine prompt
  case maybeLine of
    Nothing -> askName prompt
    Just s  -> return $ Name s

askNames :: String -> REPL [Name]
askNames prompt = do
  maybeLine <- liftInput $ HL.getInputLine prompt
  case maybeLine of
    Nothing -> askNames prompt
    Just s  -> return $ map Name (splitByComma (trimSpace s))
  where
    splitBy :: (a -> Bool) -> [a] -> [[a]]
    splitBy p [] = []
    splitBy p xs = a:(splitBy p $ dropWhile p $ b)
      where
        (a, b) = break p xs

    splitByComma :: String -> [String]
    splitByComma = splitBy (== ',')

askNum :: String -> REPL Int
askNum prompt = do
  maybeLine <- liftInput $ HL.getInputLine prompt
  case maybeLine of
    Nothing -> askNum prompt
    Just s  -> return $ read s
