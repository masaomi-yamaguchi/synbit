{-# LANGUAGE PatternSynonyms, CPP, ViewPatterns #-}

-- {-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
--
module Syntax.Aux where

import           Control.Arrow (first)
import           Control.Monad (ap, join, msum, foldM)
import           Data.Function (on)
import           Data.List (groupBy)
import           Debug.Trace
import           Err hiding (err)
import           Name
import           Syntax.Lexer
import           Syntax.Type
import           SrcLoc
import           Data.Monoid

ddump :: String -> a -> a

#ifdef DEBUG
ddump = trace

#else
ddump = flip const
#endif

mkL0 = L noSrcSpan

spans :: [Located a] -> SrcSpan
spans = mconcat . map getLoc

num :: Located Token -> Integer
num (unLoc -> TkNumber n) = n

str :: Located Token -> String
str (unLoc -> TkString s) = s
str (unLoc -> TkVarId s) = s
str (unLoc -> TkConId s) = s

char :: Located Token -> Char
char (unLoc -> TkChar c) = c

name :: Located Token -> Name
name = Name . str

cname :: Located Token -> Name
cname = CName . str

makeVar :: Located Token -> LExp
makeVar t = L (getLoc t) $ EVar (name t)

makeCon :: Located Token -> LExp
makeCon t = L (getLoc t) $ ECon False (cname t) []

makeTup :: [LExp] -> LExp
makeTup [e] = e
makeTup es = L (spans es) $ ECon False NTup es

makeList :: SrcSpan -> [LExp] -> LExp
makeList s [] = L s (ECon False NNil [])
makeList s (e:es) = let e' = makeList s es
                    in L s $ ECon False NCons [e, e']

makeString :: SrcSpan -> String -> LExp
makeString span ss = makeList span $ map (mkL0 . EChar) ss

makeApp :: LExp -> LExp -> LExp
makeApp (L i (ECon b c es)) e2 = L (i <> getLoc e2) (ECon b c $ es ++ [e2])
makeApp e1@(L i _) e2 = L (i <> getLoc e2) (EApp e1 e2)

makeComp :: LExp -> LExp -> LExp
makeComp e1 e2 = makeApp (makeApp (mkL0 $ EVar $ Name "comp") e1) e2

makeListPat :: [LPat] -> LPat
makeListPat [] = mkL0 $ PCon NNil []
makeListPat (p:ps) = let p' = makeListPat ps
                     in L (getLoc p <> getLoc p') $ PCon NCons [p, p']

makeTupPat :: [LPat] -> LPat
makeTupPat [p] = p
makeTupPat ps = L (spans ps) $ PCon NTup ps

makeAbsB :: LPat -> LExp -> Alex LExp
makeAbsB (L s1 (PVar x)) e = return $ L (s1 <> getLoc e) (EAbs x e)
makeAbsB p e = do
  x <- newName
  let i = getLoc p <> getLoc e
  let exp = L i
        $ EAbs x
        $ L i
        $ ECaseB (mkL0 $ EVar x) [(p, true, Branch e constTrue r)]
  return exp
  where
    r = mkL0 $ EAbs (Name "x") $ mkL0 $ EAbs NWild $ mkL0 $ EVar (Name "x")

makeAbs :: LPat -> LExp -> Alex LExp
makeAbs (L s1 (PVar x)) e = return $ L (s1 <> getLoc e) (EAbs x e)
makeAbs p e = do
  x <- newName
  let i = getLoc p <> getLoc e
  let exp = L i $ EAbs x $ L i $ ECase (mkL0 $ EVar x) [(p, true, e)]
  return exp

makeAbss :: [LPat] -> LExp -> Alex LExp
makeAbss ns e0 = foldM (\e x -> makeAbs x e) e0 ns

makeLets :: [(LPat, LExp)] -> LExp -> Alex LExp
makeLets [] e = return e
makeLets (b:binds) e2 = do
  e2' <- makeLets binds e2
  makeLet b e2'

makeLetsB :: [(LPat, LExp)] -> LExp -> Alex LExp
makeLetsB [] e = return e
makeLetsB (b:binds) e2 = do
  e2' <- makeLetsB binds e2
  makeLetB b e2'

exLF :: Located a -> Located b -> Located b
exLF span (L s e) = L (getLoc span <> s) e

exLL :: Located a -> Located b -> Located c -> Located c
exLL s1 s2 (L s e) = L (getLoc s1 <> s <> getLoc s2) e

-- makeLet :: (LPat, LExp) -> LExp -> Alex LExp
-- makeLet (p, e1) e2 = do
--   abs <- makeAbs p e2
--   return $ makeApp abs e1
makeLet :: (LPat, LExp) -> LExp -> Alex LExp
makeLet (p, e0) e = do
  let i = getLoc p <> getLoc e
  return $ L i $ ECase e0 [(p, true, e)]

makeLetB :: (LPat, LExp) -> LExp -> Alex LExp
makeLetB (p, e1) e2 = do
  abs <- makeAbsB p e2
  return $ makeApp abs e1

makeAbort :: LExp -> LExp
makeAbort e = L (getLoc e) $ EAbort e

-- makeLift :: LExp -> LExp -> LExp -> LExp
-- makeLift e1 e2 e3 = L (spans [e1,e2,e3]) $ ELift e1 e2 (Just e3)
makeLift :: LExp -> LExp -> LExp
makeLift e1 e2 = L (spans [e1, e2]) $ ELift e1 e2

makeLiftInj :: LExp -> LExp -> LExp
makeLiftInj e1 e3 = let e2 = L (getLoc e3) $ EAbs NWild e3
                    in L (getLoc e1 <> getLoc e2) $ ELift e1 e2

makeCons :: LExp -> LExp -> LExp
makeCons e1 e2 = L (spans [e1, e2]) $ ECon False NCons [e1, e2]

makeAdd :: LExp -> LExp -> LExp
makeAdd e1 e2 = L (spans [e1, e2]) $ EAdd e1 e2

makeSub :: LExp -> LExp -> LExp
makeSub e1 e2 = L (spans [e1, e2]) $ EAdd e1 (L (getLoc e2) $ ENeg e2)

makeCaseB :: LExp -> [(LPat, LGuard, Branch)] -> LExp
makeCaseB e alts = L (getLoc e <> mconcat (map getLocAlt alts)) $ ECaseB e alts
  where
    getLocAlt (p, g, b) = getLoc p <> getLoc g <> getLocBranch b

    getLocBranch (Branch e cond r) = getLoc e <> getLoc cond <> getLoc r

makeCase :: LExp -> [(LPat, LGuard, LExp)] -> LExp
makeCase e alts = L (getLoc e <> mconcat (map getLocAlt alts)) $ ECase e alts
  where
    getLocAlt (p, g, e) = getLoc p <> getLoc g <> getLoc e

constTrue :: LExp
constTrue = mkL0 $ EAbs NWild true

true :: LExp
true = mkL0 $ ECon False NTrue []

-- makeIfEq :: Name -> Name -> LExp -> LExp
-- makeIfEq x y e = L (getLoc e) $ EIfEq x y e
makeIf :: LExp -> LExp -> LExp -> LExp
makeIf e0 e1 e2 = L (spans [e0, e1, e2])
  $ ECase
    e0
    [(mkL0 (PCon NTrue []), true, e1), (mkL0 (PCon NFalse []), true, e2)]

--
-- makeDiscardable :: Name -> LExp -> LExp -> LExp
-- makeDiscardable n e1 e2 =
--   L (spans [e1,e2]) $ EDiscard n e1 e2
openBContext :: LExp -> Alex LExp
openBContext (L i e) = L i <$> openBContext_ i e

openBContext_ :: SrcSpan -> Exp -> Alex Exp
openBContext_ i (ECon False n es) = ECon True n <$> mapM openBContext es
openBContext_ i (ECon True n es) = return $ ECon True n es -- already proced
-- openBContext_ i (EDiscard x e1 e2) = EDiscard x e1 <$> openBContext e2
openBContext_ i (ECase e alts) = ECase e
  <$> mapM
    (\(p, g, e) -> do
       e' <- openBContext e
       return (p, g, e'))
    alts
openBContext_ i (ECaseB e alts) = ECaseB <$> openBContext e
  <*> mapM
    (\(p, g, Branch e c r) -> do
       e' <- openBContext e
       return (p, g, Branch e' c r))
    alts
-- Let expression
openBContext_ i (EApp (L j (EAbs x e1)) e2) = do
  e1' <- openBContext e1
  return $ EApp (L j (EAbs x e1')) e2
openBContext_ i (ENum k) = return $ EConstL $ L i (ENum k)
openBContext_ i (EChar k) = return $ EConstL $ L i (EChar k)
openBContext_ i e@(EAdd _ _) = errSrcInfo i
  $ "Unidirectional " ++ show e ++ " appears in a bidirectional context."
openBContext_ i e@(EAbs _ _) = errSrcInfo i
  $ "Unidirectional " ++ show e ++ " appears in a bidirectional context."
openBContext_ i e@(EEq _ _) = errSrcInfo i
  $ "Unidirectional " ++ show e ++ " appears in a bidirectional context."
openBContext_ i e@(ELess _ _) = errSrcInfo i
  $ "Unidirectional " ++ show e ++ " appears in a bidirectional context."
openBContext_ i e = return e

-- errSrcInfo :: Show i => i -> String -> D a
errSrcInfo i s = lexError $ "[" ++ show i ++ "] " ++ s

data PreDecl = PreDecl Name [LPat] LExp
             | PreDeclT Name Ty

instance Show PreDecl where
  show (PreDecl n ps e) =
    "PreDecl  " ++ show n ++ " " ++ show ps ++ " (" ++ show e ++ ")"
  show (PreDeclT n t) = "PreDeclT " ++ show n ++ " (" ++ show t ++ ")"

nameOf :: Located PreDecl -> Name
nameOf (L _ (PreDecl n _ _)) = n
nameOf (L _ (PreDeclT n _)) = n

extractTyDecl :: [Located PreDecl] -> Alex (Maybe Ty)
extractTyDecl ds = go Nothing (map unLoc ds)
  where
    go r [] = return r
    go Nothing (PreDeclT _ t:ds) = go (Just t) ds
    go (Just k) (PreDeclT f _:ds) =
      lexError $ "Multiple type signatures for " ++ show f
    go r (_:ds) = go r ds

newName :: Alex Name
newName = do
  i <- nextUniqueInt
  return $ NameI i

-- FIXME: Currently it does not support no bidirectional pattern matching
makeDecls :: [Located PreDecl] -> Alex [LDecl]
makeDecls decls = mapM makeDeclsAux $ groupBy ((==) `on` nameOf) decls

makeDeclsAux :: [Located PreDecl] -> Alex LDecl
makeDeclsAux decls
  | Just (f, args, e) <- onePreDecl Nothing decls, all isVariable args = do
    ty <- extractTyDecl decls
    makeDecl (mconcat $ map getLoc decls) f args e ty
  where
    onePreDecl r [] = r
    onePreDecl Nothing (L _ (PreDecl f args e):ds) =
      onePreDecl (Just (f, args, e)) ds
    onePreDecl _ (L _ (PreDecl f args e):ds) = Nothing
    onePreDecl r (_:ds) = onePreDecl r ds

    isVariable (L _ (PVar _)) = True
    isVariable _ = False
makeDeclsAux decls_ = do
  let nargs = length (args $ head decls)
  let ns = [0 .. nargs - 1]
  let span = mconcat $ map loc decls
  let func = fname (head decls)
  names <- mapM (const newName) ns
  let v k = names !! k
  let exp0 = makeTup [mkL0 $ EVar (v k) | k <- ns]
  let exp = L span $ ECase exp0 $ map makeAlt decls
  ty <- extractTyDecl decls_
  makeDecl span func [mkL0 (PVar (v k)) | k <- ns] exp ty
  where
    decls = [(i, f, a, e) | L i (PreDecl f a e) <- decls_]

    loc (i, _, _, _) = i

    fname (_, f, _, _) = f

    args (_, _, a, _) = a

    v = NameI

    makeAlt (_, _, ps, e) = (makeTupPat ps, true, e)

makeDecl :: SrcSpan -> Name -> [LPat] -> LExp -> Maybe Ty -> Alex LDecl
makeDecl span func args exp ty = do
  e' <- foldr (\n e -> e >>= makeAbs n) (return exp) args
  return $ L span $ Decl func ty e'

data OPat -- Oneway patterns
  = OVar Name
  | OCon Name [OPat]
  | ONum Integer
  | OChar Char
  | OView (LExp -> LExp) OPat -- view pattern

introCheckMatch :: [OPat] -> LExp -> Alex LExp
introCheckMatch ps e = do
  es' <- mapM (flip go e) ps
  return $ mfoldr eOrElse eFalse es'
  where
    -- foldr on monoid structure
    mfoldr f e [] = e
    mfoldr f e [x] = x
    mfoldr f e (x:xs) = f x (mfoldr f e xs)

    -- eApp e1 e2 = WithInfo i $ EApp e1 e2
    eTrue = mkL0 $ ECon False NTrue []

    eFalse = mkL0 $ ECon False NFalse []

    eAndAlso e1 e2 = makeApp (makeApp (mkL0 (EVar (Name "andAlso"))) e1) e2

    eOrElse e1 e2 = makeApp (makeApp (mkL0 (EVar (Name "orElse"))) e1) e2

    convertPat :: OPat -> Alex (LPat, [(Name, (LExp -> LExp, OPat))])
    convertPat (OVar x) = return (mkL0 $ PVar x, [])
    convertPat (ONum k) = return (mkL0 $ PNum k, [])
    convertPat (OChar k) = return (mkL0 $ PChar k, [])
    convertPat (OView f p) = do
      n <- newName
      return (mkL0 $ PVar n, [(n, (f, p))])
    convertPat (OCon n ps) = do
      (ps', binds) <- unzip <$> mapM convertPat ps
      return (mkL0 $ PCon n ps', concat binds)

    go :: OPat -> LExp -> Alex LExp
    go p e = do
      (p', bind) <- convertPat p
      es' <- mapM (\(n, (f, p)) -> go p (f (mkL0 $ EVar n))) bind
      case unLoc p' of
        PVar NWild -> return eTrue
        PVar n     -> return
          $ makeApp (mkL0 $ EAbs n $ mfoldr eAndAlso eTrue es') e
        _          -> return
          $ mkL0
          $ ECase
            e
            [ (p', eTrue, mfoldr eAndAlso eTrue es')
            , (mkL0 $ PVar NWild, eTrue, eFalse)]

    -- go (OVar _) e = return eTrue
    -- go (OCon n ps) e = do
    --   ns <- mapM (const newName) ps
    --   es <- zipWithM (\p n -> go p (WithInfo noInfo $ EVar n)) ps ns
    --   return $ WithInfo noInfo $ ECase e
    --     [ ( PCon n (map PVar ns), foldr eAndAlso eTrue es, constTrue noInfo),
    --       ( PVar NWild,           eFalse, constTrue noInfo) ]
    -- go (ONum k) e =
    -- go _ e = return eTrue
-- | Very rough conditional inference
inferCond :: LExp -> Alex LExp
inferCond e0 = do
  x <- newName
  let ps = makePat e0 []
  e' <- introCheckMatch ps (mkL0 $ EVar x)
  return $ mkL0 $ EAbs x e'
  where
    makePat (L i e) = makePat_ e

    makePat_ (EVar x) binds = case lookup x binds of
      Just p  -> return p
      Nothing -> return $ OVar NWild
    makePat_ (ECon _ n es) binds = do
      ps <- mapM (\e -> makePat e binds) es
      return $ OCon n ps
    makePat_ (ENum n) binds = return $ ONum n
    makePat_ (EChar c) binds = return $ OChar c
    makePat_ (EApp (L _ (EAbs x e1)) e2) binds = do
      p <- makePat e2 binds
      makePat e1 ((x, p):binds)
    makePat_ (ENeg e) binds = do
      p <- makePat e binds
      return $ OView (mkL0 . ENeg) p
    makePat_ (EAdd e1 e2) binds = do
      p1 <- makePat e1 binds
      p2 <- makePat e2 binds
      case (p1, p2) of
        (ONum k1, ONum k2) -> return $ ONum (k1 + k2)
        (ONum k1, _) -> return $ OView (`esub` k1) p2
        (_, ONum k2) -> return $ OView (`esub` k2) p1
        _ -> return $ OVar NWild
      where
        esub e k = mkL0 (EAdd e (mkL0 (ENeg (mkL0 (ENum k)))))
    -- makePat_ (EDiscard _ _ e2) binds = makePat e2 binds
    makePat_ (ECaseB _ alts) binds =
      simpl $ msum [makePat e binds | (p, g, Branch e cond _) <- alts]
    makePat_ (ECase _ alts) binds =
      simpl $ msum [makePat e binds | (p, g, e) <- alts]
    makePat_ (EConstL e) binds = makePat e binds
    makePat_ _ binds = return $ OVar NWild

    isWild (OVar NWild) = True
    isWild _ = False

    simpl ps
      | any isWild ps = return $ OVar NWild
      | otherwise = ps

makeReconciler :: (LPat, LGuard) -> [(LPat, LExp)] -> Alex LExp
makeReconciler (pat, guard) binds = do
  e <- makeExp pat guard
  r <- makeLets binds e
  return $ mkL0 $ EAbs NWild $ mkL0 $ EAbs NWild r
  where
    makeExp pat guards = makeAssert guard (p2e pat)

    p2e :: LPat -> LExp
    p2e (L s (PVar x)) = L s (EVar x)
    p2e (L s (PCon c ps)) = L s (ECon False c (map p2e ps))
    p2e (L s (PChar c)) = L s (EChar c)
    p2e (L s (PNum n)) = L s (ENum n)

    makeAssert guard e = do
      n <- newName
      return $ mkL0 $ ECase e [(mkL0 $ PVar n, guard, mkL0 $ EVar n)]

parseError :: Located Token -> Alex a
parseError (L s TkEOF) = lexError $ "Parse error on the end of the input."
parseError tk = lexError
  $ "Parse error near the token `" ++ tokenToString (unLoc tk) ++ "'."

tokenToString :: Token -> String
tokenToString TkIf = "if"
tokenToString TkThen = "then"
tokenToString TkElse = "else"
tokenToString TkCase = "case"
tokenToString TkCaseB = "case*"
tokenToString TkOf = "of"
tokenToString TkLet = "let"
tokenToString TkLetB = "let*"
tokenToString TkIn = "in"
tokenToString TkAbort = "abort"
tokenToString TkData = "data"
tokenToString TkType = "type"
tokenToString TkWith = "with"
tokenToString TkReconciledBy = "reconciled by"
tokenToString TkDefault = "default"
tokenToString TkLift = "lift"
tokenToString TkLift_ = "lift_"
tokenToString TkLiftInj = "liftInj"
tokenToString TkInclude = "#include"
tokenToString TkEqual = "="
tokenToString TkDEqual = "=="
tokenToString TkLess = "<"
tokenToString TkColon = ":"
tokenToString TkDColon = "::"
tokenToString TkLParen = "("
tokenToString TkRParen = ")"
tokenToString TkLBrace = "{"
tokenToString TkRBrace = "}"
tokenToString TkVLBrace = "["
tokenToString TkVRBrace = "]"
tokenToString TkLArrow = "->"
tokenToString TkLBracket = "<virtual {>"
tokenToString TkRBracket = "<virtual }>"
tokenToString TkBar = "|"
tokenToString TkSemicolon = ";"
tokenToString TkPlus = "+"
tokenToString TkMinus = "-"
tokenToString TkBang = "!"
tokenToString TkAt = "@"
tokenToString TkDollar = "$"
tokenToString TkBackslash = "\\"
tokenToString TkBackquote = "`"
tokenToString TkUnderscore = "_"
tokenToString TkLOBracket = "(|"
tokenToString TkROBracket = "|)"
tokenToString TkPeriod = "."
tokenToString TkComma = ","
tokenToString (TkChar t) = show t
tokenToString (TkString t) = show t
tokenToString (TkVarId t) = show t
tokenToString (TkConId t) = show t
tokenToString (TkNumber t) = show t
tokenToString TkEOF = "<EOF>"
tokenToString TkFuns = "#funs"
tokenToString TkRoot = "#root"
tokenToString TkNonRoots = "#nonRoots"
tokenToString TkExamples = "#examples"
