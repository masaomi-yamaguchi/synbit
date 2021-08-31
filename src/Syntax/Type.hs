{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Syntax.Type where

import           Control.DeepSeq
import           Name
import           SrcLoc
import           Text.PrettyPrint as T hiding ((<>))
import           Text.PrettyPrint.HughesPJClass as T hiding ((<>))
import           Util
import           Data.IORef (IORef)
import           Data.List (intercalate, nub)
import qualified Data.Set as S

data TyDecl = TyData TName [TyVar] [(Name, [Ty])]
            | TyType TName [TyVar] Ty

instance Show TyDecl where
  show = prettyShow

data PairNameExp = PairNameExp Name Exp

instance Pretty TyDecl where
  pPrintPrec v k (TyData t ps cnstrs) = sep
    [ text "data" <+> text (show t) <+> hsep (map pPrint ps)
    , nest 4 $ sep (pPrintConstrs (text "=") cnstrs)]
    where
      pPrintConstrs p [] = []
      pPrintConstrs p (d:ds) = (p <+> pPrintConstr d)
        :pPrintConstrs (text "|") ds

      pPrintConstr (c, ts) = pPrint c <+> hsep (map (pPrintPrec v 3) ts)
  pPrintPrec v k (TyType t ps ty) = sep
    [ text "type" <+> text (show t) <+> hsep (map pPrint ps)
    , nest 4 (text "=" <+> pPrintPrec v 3 ty)]

data Ty = TyApp TName [Ty] --
        | TyVar TyVar      -- type variable
        | TyMetaV MetaTv    -- meta variable to be substituted
        | TyForAll [TyVar] BodyTy
        | TyForAllC [TyVar] [TyVar] BodyTy
          -- constructor data T b = forall a . B a (a -> b)
        | TySyn Ty Ty    -- TySyn original replaced, where original is kept for better error message
  deriving Eq

--  deriving (Eq, Show)
instance Show Ty where
  show = prettyShow

type BodyTy = MonoTy  -- forall body. only consider rank 1

type PolyTy = Ty      -- polymorphic types

type MonoTy = Ty      -- monomorphic types

data TyVar = BoundTv Name
           | SkolemTv Name Int
  deriving Ord

data MetaTv = MetaTv Int SrcSpan TyRef

type TyRef = IORef (Maybe MonoTy)

  -- 'Just t':  the metavariable is subsutitued by t
  -- 'Nothing': the metavariable is not subsutituted yet.
instance Eq TyVar where
  BoundTv n == BoundTv m = n == m
  SkolemTv _ n == SkolemTv _ m = n == m
  _ == _ = False

instance Show TyVar where
  show (BoundTv n) = show n
  show (SkolemTv n i) = show n ++ "#" ++ show i

instance Pretty TyVar where
  pPrint = text . show

instance Eq MetaTv where
  MetaTv u _ _ == MetaTv u' _ _ = u == u'

instance Show MetaTv where
  show (MetaTv u _ _) = "$t" ++ show u

instance Pretty MetaTv where
  pPrint = text . show

--
-- data Ty = TyApp TName [Ty]
--         | TyVar Name
--
-- data TyS = TyS [Name] Ty
--
-- instance Pretty TyS where
--   pPrint (TyS [] t) = pPrint t
--   pPrint (TyS ns t) = pPrint t -- OK for now.
pattern TyArr a b = TyApp (TName "->") [a, b]

pattern TyTup xs = TyApp (TName "(,..,)") xs

pattern TyList x = TyApp (TName "[]") [x]

pattern TyB x = TyApp (TName "BX") [x]

pattern TyInt = TyApp (TName "Int") []

pattern TyBool = TyApp (TName "Bool") []

pattern TyNone = TyApp (TName "None") []

pattern TyChar = TyApp (TName "Char") []

pattern TyEither x y = TyApp (TName "Either") [x, y]

pattern TyMaybe x = TyApp (TName "Maybe") [x]

pattern TyString = TyApp (TName "String") []

(-->) :: Ty -> Ty -> Ty
(-->) = TyArr

infixr 4 -->

instance Pretty Ty where
  -- pPrintPrec = go True
  pPrintPrec = go False
    where
      go isTop v k (TyVar n) = pPrint n
      go isTop v k (TyTup ts) = parens
        (sep $ punctuate comma $ map (go False v 0) ts)
      go isTop v k (TyList t) = brackets (go False v 0 t)
      go isTop v k (TyArr t1 t2) = parensIf (k > 1)
        $ sep [go False v 2 t1, hsep [text "->", go False v 1 t2]]
      go isTop v k (TyApp tname []) = pPrint tname
      go isTop v k (TyApp tname ts) = parensIf (k > 2)
        $ hsep (pPrint tname:map (go False v 3) ts)
      go isTop v k (TyMetaV m) = pPrint m
      go isTop v k (TySyn ty _) = go isTop v k ty
      go True v k (TyForAll _ t) = go True v k t
      go False v k (TyForAll [] t) = go False v k t
      go False v k (TyForAll tvs t) = parensIf (k > 0) $ hsep [go False v 0 t]
      go isTop v k (TyForAllC tvs [] t) = go isTop v k (TyForAll tvs t)
      go isTop v k (TyForAllC tvs evs t) = parensIf (k > 0)
        $ hsep
          [ hcat
              [ hsep (map pPrint tvs)
              , text "  "
              , hsep (map pPrint evs)
              , text "."]
          , go False v 0 t]

freeTyVars :: Ty -> [TyVar]
freeTyVars t = go [] t []
  where
    go bound (TyVar t) r
      | t `elem` bound = r
      | t `elem` r = r
      | otherwise = t:r
    go bound (TyApp _ ts) r = foldr (go bound) r ts
    go bound (TyForAll tvs t) r = go (tvs ++ bound) t r
    go bound (TyForAllC tvs etvs t) r = go (tvs ++ etvs ++ bound) t r
    go bound (TyMetaV _) r = r
    go bound (TySyn ty _) r = go bound ty r -- Ok, resolving synoynym does not change the free vars

metaTyVars :: [Ty] -> [MetaTv]
metaTyVars = foldr go []
  where
    go (TyVar _) r = r
    go (TyMetaV m) r
      | m `elem` r = r
      | otherwise = m:r
    go (TyApp _ ts) r = foldr go r ts
    go (TyForAll _ t) r = go t r
    go (TyForAllC _ _ t) r = go t r
    go (TySyn _ ty) r = go ty r

-- -> の左側に出てきたmetaTyVarsだけを集める
metaTyVars_ :: [Ty] -> [MetaTv]
metaTyVars_ = foldr (go False) []
  where
    go b (TyVar _) r = r
    go b (TyMetaV m) r
      | m `elem` r || b == False = r
      | otherwise = m:r
    go b (TyApp (TName "->") [t1, t2]) r = go True t1 (go b t2 r)
    go b (TyApp _ ts) r = foldr (go b) r ts
    go b (TyForAll _ t) r = go b t r
    go b (TyForAllC _ _ t) r = go b t r
    go b (TySyn _ ty) r = go b ty r

tyVarBinders :: BodyTy -> [TyVar]
tyVarBinders ty = nub (binders ty)
  where
    binders (TyForAll bs t) = bs ++ binders t
    binders (TyApp _ ts) = concatMap binders ts
    binders (TySyn ty _) = binders ty
    binders _ = []

tyVarName :: TyVar -> Name
tyVarName (BoundTv t) = t
tyVarName (SkolemTv t _) = t

type Prog = [Located Decl]

type LDecl = Located Decl

data Decl = Decl Name (Maybe PolyTy) LExp

instance Pretty Decl where
  pPrint (Decl n tm e) = T.hsep
    [ text (show n)
    , maybe T.empty (\t -> T.hsep [text "::", pPrint t]) tm
    , T.text "="
    , pPrint e]

  pPrintList _ ds = T.vcat $ map pPrint ds

instance Show PairNameExp where
  show = prettyShow

  showList ds = (prettyShow ds ++)

instance Pretty PairNameExp where
  pPrint (PairNameExp n e) = T.hsep [text (show n), T.text "=", pPrint e]

  pPrintList _ ds = T.vcat $ map pPrint ds

instance Show Decl where
  show = prettyShow

  showList ds = (prettyShow ds ++)

type LExp = Located Exp

data Exp =
    EVar Name
  | EAbs Name LExp
  | EApp LExp LExp
  | EAdd LExp LExp
  | EEq LExp LExp
  | ELess LExp LExp
  | ENeg LExp
  | ENum Integer
  | EChar Char
    -- | EDiscard Name LExp LExp
    --  | ELift    LExp LExp (Maybe LExp)
  | ELift LExp LExp
  | EAbort LExp
  | ECon Bool Name [LExp]
  | ECase LExp [Alt]
  | ECaseB LExp [BAlt]
  | EConstL LExp -- lifting pure values to bidiretional world

--  | EIfEq    Name Name LExp
type Alt = (LPat, LGuard, LExp)

type BAlt = (LPat, LGuard, Branch)

type LGuard = LExp

data Branch = Branch { body :: LExp, exitCond :: LExp, reconciler :: LExp }

-- -- Some of "smart" constructors
-- eVar :: Name -> Exp a
-- eVar x = WithInfo noInfo $ EVar x
-- eAbs :: Name -> Exp a -> Exp a
-- eAbs x e = WithInfo noInfo $ EAbs x e
-- eApp :: Exp a -> Exp a -> Exp a
-- eApp e1 e2 = WithInfo noInfo $ EApp e1 e2
-- eAdd :: Exp a -> Exp a -> Exp a
-- eAdd e1 e2 = WithInfo noInfo $ EAdd e1 e2
-- eEq :: Exp a -> Exp a -> Exp a
-- eEq e1 e2 = WithInfo noInfo $ EEq e1 e2
-- eELess :: Exp a -> Exp a -> Exp a
-- eELess e1 e2 = WithInfo noInfo $ ELess e1 e2
-- eNeg :: Exp a -> Exp a
-- eNeg = WithInfo noInfo . ENeg
-- eNum :: Integer -> Exp a
-- eNum = WithInfo noInfo . ENum
-- eChar :: Char -> Exp a
-- eChar = WithInfo noInfo . EChar
-- eCon :: Name -> [Exp a] -> Exp a
-- eCon n es = WithInfo noInfo $ ECon False n es
-- eTup :: [Exp a] -> Exp a
-- eTup [e] = e
-- eTup es  = eCon NTup es
-- eCaseB :: Exp a -> [BAlt a] -> Exp a
-- eCaseB e alts = WithInfo noInfo $ ECaseB e alts
instance NFData Exp where
  rnf (EVar x) = rnf x
  rnf (EAbs x e) = rnf (x, e)
  rnf (EApp e1 e2) = rnf (e1, e2)
  rnf (EAdd e1 e2) = rnf (e1, e2)
  rnf (EEq e1 e2) = rnf (e1, e2)
  rnf (ELess e1 e2) = rnf (e1, e2)
  rnf (ENeg e) = rnf e
  rnf (ENum e) = rnf e
  rnf (EChar e) = rnf e
  -- rnf (EDiscard x e1 e2) = rnf (x, e1, e2)
  --rnf (ELift e1 e2 e3)   = rnf (e1, e2, e3)
  rnf (ELift e1 e2) = rnf (e1, e2)
  rnf (EAbort e) = rnf e
  rnf (ECon b e1 e2) = rnf (b, e1, e2)
  rnf (ECase e es) = rnf (e, es)
  rnf (ECaseB e es) = rnf (e, es)
  rnf (EConstL e) = rnf e

--  rnf (EIfEq x y e) = rnf (x, y, e)
--  rnf (EGet e) = rnf e
--  rnf (EPut e) = rnf e
freeVars :: LExp -> [Name]
freeVars = S.toList . S.fromList . go []
  where
    go r (L _ e) = go_ r e

    go_ r (EVar x) = x:r
    go_ r (EAbs x e) = S.toList $ S.delete x (S.fromList (go r e))
    go_ r (EApp e1 e2) = go (go r e1) e2
    go_ r (EAdd e1 e2) = go (go r e1) e2
    go_ r (EEq e1 e2) = go (go r e1) e2
    go_ r (ELess e1 e2) = go (go r e1) e2
    go_ r (ENeg e) = go r e
    go_ r (ENum e) = r
    go_ r (EChar e) = r
    --    go_ r (EDiscard x e1 e2) = go (go (x:r) e1) e2
    --go_ r (ELift e1 e2 e3)   = go (go (maybe r (go r) e3) e1) e2
    go_ r (ELift e1 e2) = go (go r e1) e2
    go_ r (EAbort _) = r
    go_ r (ECon _ n es) = foldl go r es
    go_ r (ECase e alts) = goAlts (go r e) alts
    go_ r (ECaseB e alts) = goAltsB (go r e) alts
    go_ r (EConstL e) = go r e

    --    go_ r (EIfEq x y e)   = go (x:y:r) e
    --    go_ r (EGet e) = go r e
    --    go_ r (EPut e) = go r e
    goAlts r [] = r
    goAlts r ((p, g, e):alts) = go
      (goAlts
         (S.toList $ S.difference (S.fromList $ go r e) (S.fromList $ goP p))
         alts)
      g

    goAltsB r [] = r
    goAltsB r ((p, g, Branch e cond re):alts) = go
      (goAltsB
         (let r' = S.toList
                $ S.difference (S.fromList $ go r e) (S.fromList $ goP p)
              r'' = go r' re -- maybe r' (go r') re
          in go r'' cond)
         alts)
      g

    goP = goP' []

    goP' r (L _ p) = goP_ r p

    goP_ r (PVar x) = x:r
    goP_ r (PCon _ ps) = foldl goP' r ps
    goP_ r _ = r

isTrue :: LExp -> Bool
isTrue (L _ (ECon False NTrue [])) = True
isTrue _ = False

instance NFData Branch where
  rnf (Branch e1 e2 e3) = rnf (e1, e2, e3)

instance Pretty Exp where
  pPrintPrec v k (EVar x) = text (show x)
  pPrintPrec v k (EAbs x e) = parensIf (k > precAbs)
    $ T.hsep
      [ T.hcat [T.text "\\", text (show x)] <+> T.text "->"
      , pPrintPrec v precAbs e]
  pPrintPrec v k (EApp e1 e2) = parensIf (k > precApp)
    $ T.hsep [pPrintPrec v precApp e1, pPrintPrec v (precApp + 1) e2]
  pPrintPrec v k (EConstL e) = parensIf (k > precApp)
    $ T.hcat [text "!", pPrintPrec v (precApp + 1) e]
  pPrintPrec v k (EAdd e1 e2) = ppOp v k precAdd AssocLeft "+" e1 e2
  pPrintPrec v k (EEq e1 e2) = ppOp v k 4 NoAssoc "==" e1 e2
  pPrintPrec v k (ELess e1 e2) = ppOp v k 4 NoAssoc "<" e1 e2
  pPrintPrec v k (ENeg e) = parensIf (k > precAdd)
    $ T.sep [text "-", pPrintPrec v (precAdd + 1) e]
  pPrintPrec v k (ENum n) = text (show n)
  pPrintPrec v k (EChar c) = text (show c)
  -- pPrintPrec v k (ELift e1 e2 (Just e3)) =
  --   parensIf (k > precApp) $
  --   T.hsep [ text "lift", pPrintPrec v (precApp+1) e1, pPrintPrec v (precApp+1) e2, pPrintPrec v (precApp+1) e3]
  pPrintPrec v k (ELift e1 e2) = parensIf (k > precApp)
    $ T.hsep
      [ text "lift"
      , pPrintPrec v (precApp + 1) e1
      , pPrintPrec v (precApp + 1) e2]
  -- pPrintPrec v k (ELift e1 e2 Nothing) =
  --   parensIf (k > precApp) $
  --   T.hsep [ text "lift_", pPrintPrec v (precApp+1) e1, pPrintPrec v (precApp+1) e2 ]
  -- pPrintPrec v k (EDiscard x e1 e2) =
  --   parensIf (k > 0) $
  --   T.vcat [ T.hsep [T.text "let default", text (show x), T.text "=",
  --                    pPrintPrec v 0 e1],
  --            text "in", nest 4 $ pPrintPrec v 0 e2 ]
  pPrintPrec v k (EAbort e) = parensIf (k > precApp)
    $ hsep [text "abort", pPrintPrec v (precApp + 1) e]
  pPrintPrec v k (ECaseB e0 alts) = parensIf (k > 0)
    $ T.vcat
      [ T.hsep [T.text "case*", pPrintPrec v 0 e0, T.text "of"]
      , nest 4 $ ppAlts alts]
    where
      ppAlts alts = T.vcat
        $ map (\(p, g, Branch e cond r) -> ppAlt p g e cond r) alts

      ppAlt p g e cond r =
        if isTrue g
        then T.sep
          [ T.hsep [pPrint p, T.text "->"]
          , nest 4 (pPrintPrec v 0 e)
          , nest 4 $ T.hsep [T.text "with", pPrintPrec v precApp cond]
            -- (case r of
            --     Just exp ->
          , nest 4
            $ T.hsep [T.text "reconciled", T.text "by", pPrintPrec v precApp r]]
        else T.sep
          [ T.hsep [pPrint p, T.text "|", pPrint g, T.text "->"]
          , nest 4 (pPrintPrec v 0 e)
          , nest 4 $ T.hsep [T.text "with", pPrintPrec v precApp cond]
            -- (case r of
            --     Just exp ->
          , nest 4
            $ T.hsep [T.text "reconciled", T.text "by", pPrintPrec v precApp r]]
                          -- _ ->
                        --   T.empty)
  pPrintPrec v k (ECase e0 alts) = parensIf (k > 0)
    $ T.vcat
      [ T.hsep [T.text "case", pPrintPrec v 0 e0, T.text "of"]
      , nest 4 $ ppAlts alts]
    where
      ppAlts alts = T.vcat $ map (\(p, g, e) -> ppAlt p g e) alts

      ppAlt p g e =
        if isTrue g
        then T.sep [T.hsep [pPrint p, T.text "->"], nest 4 (pPrintPrec v 0 e)]
        else T.sep
          [ T.hsep [pPrint p, T.text "|", pPrint g, T.text "->"]
          , nest 4 (pPrintPrec v 0 e)]
  -- pPrintPrec v k (EIfEq x y e) =
  --   parensIf (k > precApp) $
  --   T.hsep [ text "ifEq*", text (show x), text (show y), pPrintPrec v (precApp+1) e]
  -- pPrintPrec v k (EBCon NNil []) = text "![]"
  -- pPrintPrec v k e | Just s  <- isStringLikeB e = hcat [text "!", text (show s)]
  -- pPrintPrec v k e | Just es <- isListLikeB   e =
  --   hcat [ text "[!", sep (punctuate comma $ map (pPrintPrec v 0) es), text "!]"]
  -- pPrintPrec v k (EBCon n es) =
  --   case n of
  --     NTup -> hcat [text "(!", sep (punctuate comma $ map (pPrintPrec v 0) es), text "!)"]
  --     NCons | [e1, e2] <- es ->
  --       ppOp v k precCons AssocRight ":!" e1 e2
  --     _ ->
  --       case es of
  --         [] -> hcat [text "!", pPrint n]
  --         _  ->
  --               parensIf (k > precApp) $
  --               T.hsep (hcat [text "!", pPrint n] : map (pPrintPrec v (precApp+1)) es)
  pPrintPrec v k (ECon b NNil []) = if b
                                    then text "![]"
                                    else text "[]"
  pPrintPrec v k e
    | Just s <- isStringLike e = text (show s)
  pPrintPrec v k e
    | Just es <- isListLike e =
      brackets $ sep $ punctuate comma $ map (pPrintPrec v 0) es
  pPrintPrec v k e
    | Just es <- isListLikeB e = sep
      [ text "(| ["
      , sep (punctuate comma $ map (pPrintPrec v 0) es)
      , text "] |)"]
  pPrintPrec v k (ECon b n es) = case n of
    NTup  -> if b
             then bbrackets $ sep (punctuate comma $ map (pPrintPrec v 0) es)
             else parens $ sep $ punctuate comma $ map (pPrintPrec v 0) es
    NCons
      | [e1, e2] <- es -> (\d -> if b
                                 then bbrackets d
                                 else d)
        $ ppOp v k precCons AssocRight ":" e1 e2
    _     -> case es of
      [] -> if b
            then hcat [pPrint n, text ""]
            else pPrint n
      _  -> let d = if b
                    then hcat [pPrint n, text ""]
                    else pPrint n
            in parensIf (k > precApp)
               $ T.hsep (d:map (pPrintPrec v (precApp + 1)) es)
    where
      bbrackets d = hcat [text "(|", d, text "|)"]

-- isStringLikeB :: Exp_ i -> Maybe String
-- isStringLikeB (EBCon NNil []) = Just ""
-- isStringLikeB (EBCon NCons [WithInfo _ (EChar c), WithInfo _ r]) =
--   (c:) <$> isStringLikeB r
-- isStringLikeB _ = Nothing
isStringLike :: Exp -> Maybe String
isStringLike (ECon False NNil []) = Just ""
isStringLike (ECon False NCons [L _ (EChar c), L _ r]) = (c:)
  <$> isStringLike r
isStringLike _ = Nothing

isListLikeB :: Exp -> Maybe [LExp]
isListLikeB (ECon True NNil []) = Just []
isListLikeB (ECon True NCons [e1, L _ r]) = (e1:) <$> isListLikeB r
isListLikeB _ = Nothing

isListLike :: Exp -> Maybe [LExp]
isListLike (ECon False NNil []) = Just []
isListLike (ECon False NCons [e1, L _ r]) = (e1:) <$> isListLike r
isListLike _ = Nothing

instance Show Exp where
  show = prettyShow

type LPat = Located Pat

data Pat = PNum Integer
         | PChar Char
         | PVar Name
         | PCon Name [LPat]

instance NFData Pat where
  rnf (PNum i) = rnf i
  rnf (PChar c) = rnf c
  rnf (PVar n) = rnf n
  rnf (PCon n ps) = rnf (n, ps)

instance Pretty Pat where
  pPrintPrec v k (PNum i) = text (show i)
  pPrintPrec v k (PChar c) = text (show c)
  pPrintPrec v k (PVar x) = text (show x)
  pPrintPrec v k (PCon NNil []) = text "[]"
  pPrintPrec v k p
    | Just s <- isStringLikeP p = text (show s)
  pPrintPrec v k p
    | Just ps <- isListLikeP p =
      brackets $ sep $ punctuate comma $ map (pPrintPrec v 0) ps
  pPrintPrec v k (PCon n ps) = case n of
    NTup  -> parens $ hcat $ punctuate comma $ map (pPrintPrec v 0) ps
    NNil
      | [] <- ps -> text "[]"
    NCons
      | [p1, p2] <- ps -> ppOp v k precCons AssocRight ":" p1 p2
    _     -> case ps of
      [] -> pPrint n
      ps -> parensIf (k > precApp)
        $ T.hsep (pPrint n:map (pPrintPrec v (precApp + 1)) ps)

isStringLikeP :: Pat -> Maybe String
isStringLikeP (PCon NNil []) = Just ""
isStringLikeP (PCon NCons [L _ (PChar c), p]) = (c:)
  <$> isStringLikeP (unLoc p)
isStringLikeP _ = Nothing

isListLikeP :: Pat -> Maybe [LPat]
isListLikeP (PCon NNil []) = Just []
isListLikeP (PCon NCons [p1, p2]) = (p1:) <$> isListLikeP (unLoc p2)
isListLikeP _ = Nothing

instance Show Pat where
  show = prettyShow

pattern PTup xs = PCon NTup xs
