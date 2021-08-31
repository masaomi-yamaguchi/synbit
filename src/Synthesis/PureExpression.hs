{-# OPTIONS_GHC -Wunused-imports #-}

module Synthesis.PureExpression where

import qualified Syntax.Type as T
import           Name
import           Typing (TyEnv, Synonyms)
import           SrcLoc

data Exp =
    EVar Name
  | EAbs Name Exp
  | EApp Exp Exp
  | EAdd Exp Exp
  | EEq Exp Exp
  | ELess Exp Exp
  | ENeg Exp
  | ENum Integer
  | EChar Char
  | ELift Exp Exp
  | EAbort Exp
  | ECon Bool Name [Exp] -- BoolはBXかどうかを表す．nameがNTupのとき，Tupleを表す. ユーザ定義の型もnameで管理している
  | ECase Exp [Alt]
  | ECaseB Exp [BAlt]
  | EConstL Exp -- !e のこと
  | EHole T.Ty (TyEnv, Synonyms)

size :: Exp -> Int
size (EVar x) = 1
size (EAbs x e) = 1 + size e
size (EApp e1 e2) = 1 + size e1 + size e2
size (EAdd e1 e2) = 1 + size e1 + size e2
size (EEq e1 e2) = 1 + size e1 + size e2
size (ELess e1 e2) = 1 + size e1 + size e2
size (ENeg e) = 1 + size e
size (ENum x) = 1
size (EChar x) = 1
size (ELift e1 e2) = 1 + size e1 + size e2
size (EAbort e) = 1 + size e
size (ECon b name es) = 1 + foldr ((+) . size) 0 es
size (ECase e0 alts) = 1 + foldr ((+) . go) 0 alts
  where
    go :: Alt -> Int
    go (p, g, e) = 1 + sizePat p + guardSize g + size e
size (ECaseB e0 balts) = 1 + foldr ((+) . go) 0 balts
  where
    go :: BAlt -> Int
    go (p, g, b) = 1
      + sizePat p
      + guardSize g
      + size (body b)
      + size (exitCond b)
      + size (reconciler b)
size (EConstL e) = 1 + size e
size (EHole ty _) = 1 -- I am not sure that this is a good solution.

sizePat :: Pat -> Int
sizePat (PNum i) = 1
sizePat (PChar c) = 1
sizePat (PVar x) = 1
sizePat (PCon name ps) = 1 + foldr ((+) . sizePat) 0 ps

guardSize :: Exp -> Int
guardSize (ECon False NTrue []) = 0 -- do not count (pat | True)
guardSize e = size e

  -- deriving Show
convertToExp :: Exp -> T.Exp
convertToExp = convert
  where
    convert :: Exp -> T.Exp
    convert (EVar x) = T.EVar x
    convert (EAbs x e) = T.EAbs x (noLoc $ convert e)
    convert (EApp e1 e2) = T.EApp (noLoc $ convert e1) (noLoc $ convert e2)
    convert (EAdd e1 e2) = T.EAdd (noLoc $ convert e1) (noLoc $ convert e2)
    convert (EEq e1 e2) = T.EEq (noLoc $ convert e1) (noLoc $ convert e2)
    convert (ELess e1 e2) = T.ELess (noLoc $ convert e1) (noLoc $ convert e2)
    convert (ENeg e) = T.ENeg (noLoc $ convert e)
    convert (ENum x) = T.ENum x
    convert (EChar x) = T.EChar x
    convert (ELift e1 e2) = T.ELift (noLoc $ convert e1) (noLoc $ convert e2)
    convert (EAbort e) = T.EAbort (noLoc $ convert e)
    convert (ECon b name es) = T.ECon b name (map (noLoc . convert) es)
    convert (ECase e0 alts) =
      T.ECase (noLoc $ convert e0) (map convertAlt alts)
    convert (ECaseB e0 balts) =
      T.ECaseB (noLoc $ convert e0) (map convertBAlt balts)
    convert (EConstL e) = T.EConstL (noLoc $ convert e)
    convert (EHole ty _) = T.EVar (Name $ "? :: " ++ show ty)

    convertAlt :: Alt -> T.Alt
    convertAlt
      (p, g, e) = (noLoc $ convertP p, noLoc $ convert g, noLoc $ convert e)

    convertBAlt :: BAlt -> T.BAlt
    convertBAlt (p, g, Branch { body = b, exitCond = exit, reconciler = r }) =
      ( noLoc $ convertP p
      , noLoc $ convert g
      , T.Branch { T.body = noLoc $ convert b
                 , T.exitCond = noLoc $ convert exit
                 , T.reconciler = noLoc $ convert r
                 })

    convertP :: Pat -> T.Pat
    convertP (PNum i) = T.PNum i
    convertP (PChar c) = T.PChar c
    convertP (PVar x) = T.PVar x
    convertP (PCon name ps) = T.PCon name (map (noLoc . convertP) ps)

instance Show Exp where
  show = show . convertToExp

type Alt = (Pat, Guard, Exp)

type BAlt = (Pat, Guard, Branch)

type Guard = Exp

data Branch = Branch { body :: Exp, exitCond :: Exp, reconciler :: Exp }
  deriving Show

data Pat = PNum Integer
         | PChar Char
         | PVar Name
         | PCon Name [Pat]
  deriving Show

showExpBr :: Exp -> String
showExpBr e = "(" ++ showExp e ++ ")"

showExp :: Exp -> String
showExp e = case e of
  EVar name -> show name
  EAbs name e1 -> "\\" ++ show name ++ " -> " ++ showExpBr e1
  EApp e1 e2 -> showExpBr e1 ++ " " ++ showExpBr e2
  EAdd e1 e2 -> showExpBr e1 ++ " + " ++ showExpBr e2
  EEq e1 e2 -> showExpBr e1 ++ " == " ++ showExpBr e2
  ELess e1 e2 -> showExpBr e1 ++ " < " ++ showExpBr e2
  ENeg e1 -> "-" ++ showExpBr e1
  ENum i -> show i
  EChar c -> show c
  ELift e1 e2 -> "lift " ++ showExpBr e1 ++ " " ++ showExpBr e2
  EAbort e1 -> "abort " ++ showExpBr e1
  ECon False NNil [] -> "[]"
  ECon True NNil [] -> "[]*"
  ECon b NCons [e1, l]
    -> (case showNCons l of
          Just text -> if b
                       then "[* " ++ showExp e1 ++ text ++ " *]"
                       else "[" ++ showExp e1 ++ text ++ "]"
          Nothing   -> showExpBr e1
            ++ (if b
                then " :* "
                else " : ")
            ++ showNCons2 l)
  ECon False NTup [] -> "()"
  ECon False NTup (e1:es)
    -> "(" ++ showExp e1 ++ concatMap (\e -> ", " ++ showExp e) es ++ ")"
  ECon True NTup [] -> "()*"
  ECon True NTup (e1:es)
    -> "(* " ++ showExp e1 ++ concatMap (\e -> ", " ++ showExp e) es ++ " *)"
  ECon False name es -> show name ++ concatMap (\e -> " " ++ showExpBr e) es
  ECon True name es
    -> show name ++ "*" ++ concatMap (\e -> " " ++ showExpBr e) es
  ECase e1 alts -> "case " ++ showExpBr e1 ++ " of { " ++ showAlts alts ++ " }"
  ECaseB e1 alts
    -> "case* " ++ showExpBr e1 ++ " of { " ++ showBAlts alts ++ " }"
  EConstL e1 -> "!" ++ showExpBr e1
  EHole ty h -> "□ :: " ++ show ty

showAlts :: [Alt] -> String
showAlts [] = ""
showAlts (a:alts) = go a ++ concatMap (\a -> "; " ++ go a) alts
  where
    go (p, g, e) = showPat False p ++ " | " ++ showExp g ++ " -> " ++ showExp e

showBAlts :: [BAlt] -> String
showBAlts [] = ""
showBAlts (a:alts) = go a ++ concatMap (\a -> "; " ++ go a) alts
  where
    go (p, g, Branch e cond reconcile) = showPat False p
      ++ " | "
      ++ showExp g
      ++ " -> "
      ++ showExp e
      ++ " with "
      ++ showExpBr cond
      ++ " reconciled by "
      ++ showExpBr reconcile

showNCons :: Exp -> Maybe String
showNCons (ECon _ NNil []) = Just ""
showNCons (ECon _ NCons [e, l]) = do
  tl <- showNCons l
  return $ ", " ++ showExp e ++ tl
showNCons e = Nothing

showNCons2 :: Exp -> String
showNCons2 (ECon b NNil []) = if b
                              then "[]*"
                              else "[]"
showNCons2 (ECon b NCons [e, l]) = if b
                                   then showExpBr e ++ " :* " ++ showNCons2 l
                                   else showExpBr e ++ " : " ++ showNCons2 l
showNCons2 e = showExpBr e

showPat :: Bool -> Pat -> String
showPat = go
  where
    go b p = case p of
      PNum i -> show i
      PChar c -> show c
      PVar name -> show name
      PCon NNil [] -> "[]"
      PCon NCons [p1, l]
        -> if b
           then "(" ++ go True p1 ++ " : " ++ go False l ++ ")"
           else go True p1 ++ " : " ++ go False l
      PCon NTup (p1:ps)
        -> "(" ++ go False p1 ++ concatMap (\p -> ", " ++ go False p) ps ++ ")"
      PCon name ps -> if b
                      then "("
                        ++ show name
                        ++ concatMap (\p -> " " ++ go True p) ps
                        ++ ")"
                      else show name ++ concatMap (\p -> " " ++ go True p) ps

rename :: [Name] -> Exp -> Exp
rename fs e = go e
  where
    go (EVar x) = EVar (shift x)
    go (EAbs x e) = EAbs (shift x) (go e)
    go (EApp e1 e2) = EApp (go e1) (go e2)
    go (EEq e1 e2) = EEq (go e1) (go e2)
    go (ELess e1 e2) = ELess (go e1) (go e2)
    go (ENum i) = ENum i
    go (EChar c) = EChar c
    go (ENeg e) = ENeg (go e)
    go (ELift e1 e2) = ELift (go e1) (go e2)
    go (EAbort e) = EAbort (go e)
    go (ECon b name es) = ECon b name (map go es)
    go (ECase e0 alts) = ECase (go e0) (map goAlt alts)
      where
        goAlt (p, g, e) = (goPat p, go g, go e)
    go (ECaseB e0 balts) = ECaseB (go e0) (map goBAlt balts)
      where
        goBAlt (p, g, br) = ( goPat p
                            , go g
                            , Branch { body = go (body br)
                                     , exitCond = go (exitCond br)
                                     , reconciler = go (reconciler br)
                                     })
    go (EConstL e1) = EConstL (go e1)

    goPat (PVar x) = PVar (shift x)
    goPat (PNum i) = PNum i
    goPat (PChar c) = PChar c
    goPat (PCon n l) = PCon n (map goPat l)

    shiftI = getMax (collect e) + 1

    shift :: Name -> Name
    shift name = case name of
      SName i -> Name ('x':show (i + shiftI)) -- Synthesisに使うuniqなname
      n       -> n

    getMax :: [Name] -> Int
    getMax ns = foldr
      (\name m -> case name of
         Name ('x':str) -> case readMaybe str :: Maybe Int of
           Just i  -> max i m
           Nothing -> m
         _ -> m)
      (-1)
      (ns ++ fs)

    collect :: Exp -> [Name]
    collect (EVar x) = [x]
    collect (EAbs x e) = x:collect e
    collect (EApp e1 e2) = collect e1 ++ collect e2
    collect (EEq e1 e2) = collect e1 ++ collect e2
    collect (ELess e1 e2) = collect e1 ++ collect e2
    collect (ENum _) = []
    collect (EChar _) = []
    collect (ENeg e) = collect e
    collect (ELift e1 e2) = collect e1 ++ collect e2
    collect (EAbort e) = collect e
    collect (ECon b name es) = foldr (\e l -> collect e ++ l) [] es
    collect (ECase e0 alts) = foldr (\alt l -> collectAlt alt ++ l) [] alts
      where
        collectAlt (p, g, e) = collectPat p ++ collect g ++ collect e
    collect (ECaseB e0 balts) = foldr (\alt l -> goBAlt alt ++ l) [] balts
      where
        goBAlt (p, g, br) = collectPat p
          ++ collect g
          ++ collect (body br)
          ++ collect (exitCond br)
          ++ collect (reconciler br)
    collect (EConstL e1) = collect e1

    collectPat (PVar x) = [x]
    collectPat (PNum i) = []
    collectPat (PChar c) = []
    collectPat (PCon _ l) = foldr (\p l' -> collectPat p ++ l') [] l

readMaybe :: (Read a) => String -> Maybe a
readMaybe s = case reads s of
  [(x, "")] -> Just x
  _         -> Nothing
