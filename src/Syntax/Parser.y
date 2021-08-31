{
{-# LANGUAGE NoMonomorphismRestriction #-}

module Syntax.Parser (
                      parseProgram, parseExp, parseExp2, parsePutArg, parseGetArg, parseTy, parseSpec
    ) where

import Syntax.Lexer
import Syntax.Type
import Syntax.Aux
import Name
import Err
import SrcLoc

import Data.Monoid
import Control.Monad ((<=<), liftM2, join)
import qualified Data.Set as S (toList)
}

%name pExp    Exp
%name pProg   Prog
%name pTy     TyExp
%name pPutArg PutArg
%name pGetArg GetArg
%name pSpec   Spec
%tokentype { Located Token }
%monad     { Alex }
%lexer     { lexer } { L _ TkEOF }
%error     { parseError }


%token
   "=" { L _ TkEqual }

   "data"  { L _ TkData }
   "type"  { L _ TkType }

   "let"   { L _ TkLet }
   "let*"  { L _ TkLetB }
   "in"    { L _ TkIn }
   "case"  { L _ TkCase }
   "then"  { L _ TkThen }
   "else"  { L _ TkElse }
   "case*" { L _ TkCaseB }
   "of"    { L _ TkOf }
   "if"    { L _ TkIf }
   "eq"    { L _ (TkVarId "eq") }
   "with"  { L _ TkWith }
   "reconciled_by" { L _ TkReconciledBy }
   bq     { L _ TkBackquote }

   "#include" { L _ TkInclude }
   
   "#funs" {L _ TkFuns}
   "#root" {L _ TkRoot}
   "#nonRoots" {L _ TkNonRoots}
   "#examples" {L _ TkExamples}

   "lift"    { L _ TkLift }
   "lift_"   { L _ TkLift_ }
   "liftInj" { L _ TkLiftInj }

   "abort"   { L _ TkAbort }

   "default" { L _ TkDefault }

   "["    { L _ TkLBracket }
   "]"    { L _ TkRBracket }
   "|"    { L _ TkBar }

   "{"    { L _ TkLBrace }
   "}"    { L _ TkRBrace }

   open    { L _ TkVLBrace }
   vrbrace { L _ TkVRBrace }

   ";"    { L _ TkSemicolon }

   "\\"   { L _ TkBackslash }
   "->"   { L _ TkLArrow }

   "$"    { L _ TkDollar }
   "."    { L _ TkPeriod }
   ","    { L _ TkComma }
   "+"    { L _ TkPlus }
   "-"    { L _ TkMinus }
   ":"    { L _ TkColon }
   "::"   { L _ TkDColon }

   "!"    { L _ TkBang }
   "@"    { L _ TkAt }

   "=="   { L _ TkDEqual }
   "<"   { L _ TkLess }

   "_"    { L _ TkUnderscore }

   "("    { L _ TkLParen }
   ")"    { L _ TkRParen }

   "(|"   { L _ TkLOBracket }
   "|)"   { L _ TkROBracket }

   char   { L _ (TkChar _) }
   varId  { L _ (TkVarId _) }
   conId  { L _ (TkConId _) }
   string { L _ (TkString _) }
   number { L _ (TkNumber _) }


%%

Spec :: { (String, Name, [Name], String) }
  : MaybeSemi FunsDecl ";" RootDecl ";" NonRootDecls ";" ExamplesDecl MaybeSemi { ($2,$4,$6,$8) }
   
FunsDecl :: { String }
  : "#funs" "=" string {str $3}

RootDecl :: { Name }
  : "#root" "=" varId { Name (str $3) }

NonRootDecls :: { [Name] }
  : "#nonRoots" "=" NameDecls { $3 }

NameDecls :: { [Name] }
  : varId               {[Name (str $1)]}
  | varId "," NameDecls { Name (str $1) : $3}
  | {- Empty -}         {[]}

ExamplesDecl :: { String }
  : "#examples" "=" string {str $3}


Prog :: { ([FilePath], [TyDecl], [LDecl])  }
  : "{" PreProg "}" { $2 }
  | PreProg         { $1 }

PreProg :: { ([FilePath], [TyDecl], [LDecl]) }
  : ManyDirective ";" TopDecls
           {% let (t,d) = $3 in makeDecls (reverse d) >>= \decls -> return (reverse $1, reverse t, decls) }
  | TopDecls
           {% let (t,d) = $1 in makeDecls (reverse d) >>= \decls -> return ([], reverse t, decls) }
  -- : MaybeSemi ManyDirective ManyTyDecl ManyDecl MaybeSemi
  --          {%
  --           makeDecls $4 >>= \decls -> return (reverse $2, $3, reverse decls)
  --          }

MaybeSemi
  : ";" {}
  |     {}

ManyDirective :: { [FilePath] } -- Reverse order
  : ManyDirective ";" Directive { $3 : $1 }
  | ManyDirective ";"           { $1 }
  | Directive                   { [$1] }
  | {- Empty -}                 { [] }

TopDecls :: { ([TyDecl], [Located PreDecl]) } -- Both reverse order
  : TopDecls ";" TopDecl { let (a,b) = $1 in either (\x -> (x:a,b)) (\x -> (a,x:b)) $3 }
  | TopDecls ";"         { $1 }
  | TopDecl              { either (\x -> ([x],[])) (\x -> ([],[x])) $1 }

TopDecl :: { Either TyDecl (Located PreDecl) }
  : TyDecl               { Left $1 }
  | Decl                 { Right $1 }


-- ManyDirective :: { [FilePath] }
--   :                             { []    }
--   | Directive ";" ManyDirective { $1 : $3 }

Directive :: { FilePath }
  : "#include" string { str $2 }




-- ManyTyDecl :: { [TyDecl] }
--   :           { [] }
--   | TyDecl ";" ManyTyDecl { $1 : $3 }

TyDecl :: { TyDecl }
  : "data" TyCon TyArgs "=" TyAlts { TyData $2 $3 (reverse $5) }
  | "type" TyCon TyArgs "=" TyExp  { TyType $2 $3 $5 }

TyCon :: { TName }
  : conId { TName $ str $1 }

TyArgs :: { [TyVar] }
  :       { [] }
  | TyVar TyArgs { $1 : $2 }

TyVar :: { TyVar }
  : varId { BoundTv (Name (str $1)) }

TyAlts :: { [(Name, [Ty])] }
  : TyAlt            { [$1] }
  | TyAlts "|" TyAlt { $3 : $1 }

TyAlt :: { (Name, [Ty]) }
  : conId ATyExps     { (cname $1, reverse $2) }

ATyExps :: { [Ty] }
  :                   { [] }
  | ATyExps ATyExp    { $2 : $1 }

TyExp :: { Ty }
  : TyExp1 "->" TyExp { TyArr $1 $3 }
  | TyExp1            { $1 }

TyExp1 :: { Ty }
  : TyExp1 ATyExp     { case $1 of {TyApp n xs -> TyApp n (xs++[$2])} }
  | ATyExp            { $1 }

ATyExp :: { Ty }
  : "(" TyExpsC ")"     { case $2 of { [x] -> x ; xs -> TyTup xs } }
  | "[" TyExp "]"       { TyApp (TName "[]") [$2] }
  | TyVar               { TyVar $1 }
  | TyCon               { TyApp $1 [] }

TyExpsC :: { [Ty] }
  :                       { [] }
  | TyExp                 { [$1] }
  | TyExp "," TyExpsC     { $1 : $3 }

-- ManyDecl :: { [Located PreDecl] }
--   :                    { [] }
--   | ManyDeclX Decl     { ($2 : $1) }

-- ManyDeclX :: { [Located PreDecl] }
--   :                    { [] }
--   | ManyDeclX Decl ";" { ($2 : $1) }



Decl :: { Located PreDecl }
  : varId ManyPat3 "=" Exp  { L (spans $2 <> getLoc $4) (PreDecl (name $1) (reverse $2) $4) }
  | varId "::" TyExp        { L (getLoc $1) $ -- FIXME
                              PreDeclT (name $1) (let ty = $3 in TyForAll (freeTyVars ty) ty)  }

Bind(e)
  : "{" BindCore(e) "}"    { $2 }
  | open BindCore(e) close { $2 }
--  | SingleBind(e)          { [$1] }

SingleBind(e)
  :     Pat3 "=" e { ($1, $3) }

BindCore(e)
  : SingleBind(e)                 { [$1] }
  | SingleBind(e) ";" BindCore(e) { $1 : $3 }

Exp :: { LExp }
  : "let"  Bind(Exp) "in" Exp
       {% fmap (exLF $1) (makeLets $2 $4) }
  | "let*" Bind(BExp) "in" BExp
       {% fmap (exLF $1) (makeLetsB $2 $4) }
--  | "let" "default" varId "=" Exp "in" Exp { exLF $1 $  makeDiscardable (name $3) $5 $7 }
--  | "let" open "default" varId "=" Exp close "in" Exp
--                                           { exLL $1 $> $ makeDiscardable (name $4) $6 $9 }
  | "case*" BExp "of" BAltsBlock           { exLL $1 $> $ makeCaseB $2 (reverse $ unLoc $4) }
  | "case"  Exp  "of" AltsBlock            { exLL $1 $> $ makeCase  $2 (reverse $ unLoc $4) }
  | "if"    Exp "then" Exp "else" Exp      { exLF $1 $ makeIf $2 $4 $6 }
  | "\\" SomePat3 "->" Exp                 {% fmap (exLF $1) $ makeAbss $2 $4 }
  | Exp1 "$" Exp                           { makeApp $1 $3 }
  | Exp1                                   { $1 }

BAltsBlock :: { Located [(LPat, LGuard, Branch)] }
  : "{" BAlts "}"    { exLL $1 $> $ mkL0 $2 }
  | open BAlts close { exLF $1 $ mkL0 $2 }

AltsBlock :: { Located [(LPat, LGuard, LExp)] }
  : "{" Alts "}"    { exLL $1 $> $ mkL0 $2 }
  | open Alts close { exLF $1 $ mkL0 $2 }

VarIDs :: { [Name] }
  : varId                        { [Name (str $1)] }
  | varId VarIDs                 { Name (str $1) : $2 }

Exp1 :: { LExp }
  : Exp2                         { $1 }

Exp2 :: { LExp }
  : Exp4                         { $1 }

Exp4 :: { LExp }
  : Exp5 "==" Exp5               { L (spans [$1,$3]) $ EEq $1 $3 }
  | Exp5 "<" Exp5               { L (spans [$1,$3]) $ ELess $1 $3 }
  | Exp5                         { $1 }


Exp5 :: { LExp }
  : Exp6 ":" Exp5                { makeCons $1 $3 }
  | Exp6                         { $1 }

Exp6 :: { LExp }
  : Exp6 "+" Exp7                { makeAdd $1 $3 }
  | Exp6 "-" Exp7                { makeSub $1 $3 }
  | "-" Exp7                     { L (getLoc $1 <> getLoc $2) $ ENeg $2 }
  | Exp7                         { $1 }

Exp7 :: { LExp }
  : Exp9 { $1 }

Exp9 :: { LExp }
  : Exp9 bq varId bq Exp10  { makeApp (makeApp (makeVar $3) $1) $5 }
  | Exp10 "." Exp9          { makeComp $1 $3 }
  | Exp10                   { $1 }

Exp10 :: { LExp }
  : Exp10 AtomicExp                          { makeApp $1 $2 }
--  | "eq" varId varId AtomicExp               { exLF $1 $ makeIfEq (name $2) (name $3) $4 }
  | "abort"    AtomicExp                     { exLF $1 $ makeAbort   $2 }
  -- | "lift"     AtomicExp AtomicExp AtomicExp { exLF $1 $ makeLift    $2  $3  $4 }
  | "liftInj"  AtomicExp AtomicExp           { exLF $1 $ makeLiftInj $2 $3 }
  | "lift"     AtomicExp AtomicExp           { exLF $1 $ makeLift $2 $3 }
  | AtomicExp                                { $1 }

AtomicExp :: { LExp }
  : number                       { L (getLoc $1) $ ENum $ num $1 }
  | varId                        { makeVar $1 }
  | conId                        { makeCon $1 }
  | "(|" ManyExpC "|)"           {% openBContext (exLL $1 $3 $  makeTup (reverse $2)) }
  | "(" ManyExpC ")"             { exLL $1 $3 $ makeTup (reverse $2) }
  | "[" ManyExpC "]"             { exLL $1 $3 $ makeList (getLoc $1 <> getLoc $3) (reverse $2) }
  | string                       { makeString (getLoc $1) (str $1) }
  | char                         { L (getLoc $1) (EChar $ char $1) }
  | "!"   AtomicExp              { exLF $1 $ L (getLoc $2) (EConstL $2) }

ManyExpC :: { [LExp] }
  :                           { [] }
  | ManyExpCX Exp             { $2 : $1 }

ManyExpCX :: { [LExp] }
  :                           { [] }
  | ManyExpCX Exp ","         { $2 : $1 }

Pat :: { LPat }
  : Pat1 { $1 }

Pat1 :: { LPat }
  : Pat2 ":" Pat1 { L (spans [$1,$3]) $ PCon NCons [$1, $3] }
  | Pat2          { $1 }

Pat2 :: { LPat  }
  : conId SomePat3 { L (spans $2) $ PCon (cname $1) (reverse $2) }
  | Pat3           { $1 }

SomePat3 :: { [LPat] }
  : ManyPat3 Pat3    { $2 : $1 }

ManyPat3 :: { [LPat] }
  :                  { [] }
  | ManyPat3 Pat3    { $2 : $1 }

Pat3 :: { LPat }
  : "_"              { L (getLoc $1) $ PVar NWild }
  | varId            { L (getLoc $1) $ PVar (name $1) }
  | conId            { L (getLoc $1) $ PCon (cname $1) [] }
  | number           { L (getLoc $1) $ PNum (num $1) }
  | char             { L (getLoc $1) $ PChar (char $1) }
  | string           { makeListPat (map (mkL0 .PChar) (str $1)) }
  | "[" ManyPatC "]" { exLL $1 $3 $ makeListPat (reverse $2) }
  | "(" ManyPatC ")" { exLL $1 $3 $ makeTupPat  (reverse $2) }

ManyPatC :: { [LPat] }
  :                           { [] }
  | ManyPatCX Pat             { $2 : $1 }

ManyPatCX :: { [LPat] }
  :                           { [] }
  | ManyPatCX Pat ","         { $2 : $1 }


Alts :: { [(LPat, LGuard, LExp)] }
  : Alt                        { [$1] }
  | Alts ";" Alt               { $3 : $1 }

Alt :: { (LPat, LGuard, LExp) }
  : Pat Guard "->" Exp         { ($1, $2, $4) }

BAlts :: { [(LPat, LGuard, Branch)] }
  : BAlt                       { [$1] }
  | BAlts ";" BAlt             { $3 : $1 }

BAlt :: { (LPat, LGuard, Branch) }
  : Pat Guard "->" Branch     {% $4 ($1, $2) >>= \re -> return ($1, $2, re) }

Guard :: { LGuard }
  : "|" Exp    { $2 }
  | {- Empty -} { true }

Branch :: { (LPat, LGuard) -> Alex Branch }
  : BExp WithExp ReconcileExp { \p -> pure (Branch $1) <*> $2 $1 <*> $3 p }

BExp :: { LExp }
  : Exp {% openBContext $1 }

WithExp :: { LExp -> Alex LExp}
  : "with" Exp { const (return $2) }
  |            { inferCond  }

ReconcileExp :: { (LPat, LGuard) -> Alex LExp }
  : "reconciled_by" Exp  { const (return $2) }
  | "default" Bind(Exp)  { \pg -> makeReconciler pg $2 }
  |                      { \pg -> makeReconciler pg [] }

close :: { () }
  : vrbrace { () }
  | error   {% popLayoutContext }


PutArg :: { [LExp] }
  : AtomicExp                     { [$1] }
  | AtomicExp AtomicExp           { [$1, $2] }
  | AtomicExp AtomicExp AtomicExp { [$1, $2, $3] }

GetArg :: { [LExp] }
  : AtomicExp { [$1] }
  | AtomicExp AtomicExp { [$1, $2] }
{

lexer :: (Located Token -> Alex b) -> Alex b
lexer k = alexMonadScan >>= k

parseSpec :: String -> Err (String, Name, [Name], String)
parseSpec s =
   case runAlex s (setLayoutContext [Layout 1] >> pushLexCode bol >> setFilePath "interactive" >> pSpec) of
    Left s  -> Bad s
    Right t -> Ok  t


parseProgram :: FilePath -> String -> Err ([FilePath], [TyDecl], [LDecl])
parseProgram fp s =
  case runAlex s (setLayoutContext [Layout 1] >> pushLexCode bol >> setFilePath fp >> pProg) of
    Left  s -> Bad s
    Right t -> Ok  t

parseExp :: String -> Err LExp
parseExp s =
  case runAlex s (setFilePath "interactive" >> pExp) of
    Left s  -> Bad s
    Right t -> Ok  t

parseExp2 :: String -> Err LExp
parseExp2 s =
  case runAlex s (setFilePath "interactive" >> pExp) of
    Left s  -> Bad s
    Right t -> Ok  t

parseTy :: String -> Err Ty
parseTy s =
  case runAlex s (setFilePath "interactive" >> pTy) of
    Left s  -> Bad s
    Right ty -> Ok  (TyForAll (freeTyVars ty) ty)

parsePutArg :: String -> Err [LExp]
parsePutArg s =
  case runAlex s (setFilePath "putarg" >> pPutArg) of
    Left s  -> Bad s
    Right t -> Ok t

parseGetArg :: String -> Err [LExp]
parseGetArg s =
    case runAlex s (setFilePath "getarg" >> pGetArg) of
        Left  s -> Bad s
        Right t -> Ok t
}
