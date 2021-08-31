{
{-# OPTIONS_GHC -fno-warn-tabs #-}
module Syntax.Lexer where

import Data.List (isPrefixOf)
import SrcLoc
import Debug.Trace
}

%wrapper "monadUserState"


$digit  = 0-9
$alpha  = [a-zA-Z]
@ident  = [a-z] ($alpha | $digit | "_" | "'")*
@cident = [A-Z] ($alpha | $digit | "_" | "'")*
-- @bcident = @cident "!"

@string = \" ( ($printable # [\"\\]) | "\" "\" | "\n" | "\t" | "\r" | "\" [\"] )* \" -- "
@char   = \' ( ($printable # [\'\\]) | "\" "\" | "\n" | "\t" | "\r" | "\" [\"] ) \' -- "

@op = [\= \+ \- \* \/ \< \> \$ \| \& \? \: \# \!]+
@reserved =
  if | then | else | case | of | let | in | with | where | abort |
  "#include" | discard | ("reconciled" $white+ "by") | liftInj | lift | lift_ |
  "let*" | "case*" | "if*" | type | data | pure | get | put | default |
  "ifeq*" | eq | "#funs" | "#root" | "#nonRoots" | "#examples"

$nbsp = $white # \n


@punct =
  "." | "(" | ")" | "," | "|" | "[" | "]" | "`" | "::" | "->"
  | "(|" | "|)" | "@" | "_" | "\" -- "


tokens :-
$nbsp+;


<0, comment> "{-"  { beginComment }

<comment>    "-}"  { endComment }
<comment>    [.\n];

<0,bol,layout> "--".*    ;
<bol> {
  \n;
  () { doBol }
}

-- After layouting keywords (let, letB, where, of)
<layout> {
  \{ / [^\-] { hopefullyOpenBrace }
  \n;
  () { newLayoutContext }
}



<layout_left> () { doLayoutLeft }

<0> \n { \_ _ -> pushLexCode bol >> alexMonadScan }

<0> {
  ";" { tok $ const TkSemicolon }
  "{" { openBrace }
  "}" { closeBrace }
  @punct     { mkPunct }
  @op        { mkOp }
  @reserved  { mkReserved }
  @string    { tok $ TkString . read }
  @char      { tok $ TkChar . read }
  $digit+    { tok $ TkNumber . read }
  @ident     { tok $ TkVarId }
  @cident    { tok $ TkConId }
  eof        { tok $ const TkEOF }
}


{

data LayoutContext = NoLayout | Layout !Int
type LexCode = Int

data AlexUserState
  = AUS { ausContext    :: [LayoutContext]
        , ausCodeStack  :: [LexCode]
                          -- alex_scd s is assumeted to be a stack top
        , ausFilePath   :: !FilePath
        , ausNameSource :: !Int -- for desugaring
                          --  ausPrevPosn  :: !AlexPosn,
        }

alexInitUserState :: AlexUserState
alexInitUserState = AUS [] [] "<interactive>" 0

nextUniqueInt :: Alex Int
nextUniqueInt = do
  ust <- getUST
  let src = ausNameSource ust
  setUST $ ust { ausNameSource = src + 1 }
  return src

pushLexCode :: LexCode -> Alex ()
pushLexCode code = do
  ust  <- getUST
  prev <- alexGetStartCode
  let ust' = ust { ausCodeStack = prev : ausCodeStack ust }
  setUST ust'
  alexSetStartCode code

popLexCode :: Alex LexCode
popLexCode = do
  ust <- getUST
  curr <- alexGetStartCode
  let code : rest = ausCodeStack ust
  let ust' = ust { ausCodeStack = rest }
  setUST ust'
  alexSetStartCode code
  return curr

getLayoutContext :: Alex [LayoutContext]
getLayoutContext = do
  ust <- getUST
  return $ ausContext ust

setLayoutContext :: [LayoutContext] -> Alex ()
setLayoutContext ctx = do
  ust <- getUST
  setUST $ ust { ausContext = ctx }

getUST :: Alex AlexUserState
getUST = Alex $ \s@AlexState { alex_ust = ust } -> Right (s, ust)

setUST :: AlexUserState -> Alex ()
setUST ust = seq ust $ Alex $ \s -> Right (s { alex_ust = ust }, ())


getFilePath :: Alex FilePath
getFilePath = do
  ust <- getUST
  return $ ausFilePath ust

setFilePath :: FilePath -> Alex ()
setFilePath fp = do
  ust <- getUST
  setUST (ust { ausFilePath = fp })

lexError :: String -> Alex a
lexError s = do
  fp <- getFilePath
  AlexPn _ l c <- getAlexPosn
  alexError $ show (SrcSpan fp l l c c) ++ ":\n" ++ s


popLayoutContext :: Alex ()
popLayoutContext = do
  cs <- getLayoutContext
  case cs of
    []     -> lexError "Parse error"
    (_:cs') ->
      setLayoutContext cs'

peekLayoutLevel :: Alex Int
peekLayoutLevel = do
  cs <- getLayoutContext
  case cs of
    (Layout n:_) -> -- trace ("layout: " ++ show n) $
      return n
    _            -> return $ -1

getAlexPosn :: Alex AlexPosn
getAlexPosn = Alex $ \s -> Right (s, alex_pos s)

-- getPrevPosn :: Alex AlexPosn
-- getPrevPosn = do
--   ust <- getUST
--   return $ ausPrevPosn ust


-- setPrevPosn :: AlexPosn -> Alex ()
-- setPrevPosn pos = pos `seq` do
--   ust <- getUST
--   setUST ( ust { ausPrevPosn = pos } )


type Action = AlexAction (Located Token)

doBol :: Action
doBol input len = do
  AlexPn _ _ col <- getAlexPosn
  level <- peekLayoutLevel
  span  <- getSpan input len
  case compare col level of
    LT -> do
      popLayoutContext
      return $ L span TkVRBrace
    EQ -> do
      _ <- popLexCode
      return $ L span TkSemicolon
    GT -> do
      _ <- popLexCode
      alexMonadScan

hopefullyOpenBrace :: Action
hopefullyOpenBrace input len = do
  ctx <- getLayoutContext
  AlexPn _ _ col <- getAlexPosn
  span <- getSpan input len
  case ctx of
    Layout prev_off : _ | prev_off >= col ->
      lexError "Missing block"
    _ -> do
      _ <- popLexCode
      openBrace input len

openBrace, closeBrace :: Action
openBrace input len = do
  ctx <- getLayoutContext
  setLayoutContext (NoLayout : ctx)
  span <- getSpan input len
  return $ L span TkLBrace
closeBrace input len = do
  popLayoutContext
  span <- getSpan input len
  return $ L span TkRBrace

newLayoutContext :: Action
newLayoutContext input len = do
  _ <- popLexCode
  AlexPn _ _ col <- getAlexPosn
  span <- getSpan input len
  ctx <- getLayoutContext
  case ctx of
    Layout prev_col : _ | prev_col > col -> do
      pushLexCode layout_left
      return $ L span TkVLBrace
    _ -> do
      setLayoutContext (Layout col : ctx)
      return $ L span TkVLBrace

doLayoutLeft :: Action
doLayoutLeft input len = do
  _ <- popLexCode
  span <- getSpan input len
  pushLexCode bol
  return $ L span TkVRBrace




getSpan :: AlexAction SrcSpan
getSpan input len = do
  AlexPn _ sline scol <- getAlexPosn
  fp <- getFilePath
  return $ mkSrcSpan (SrcLoc fp sline (scol - len)) (SrcLoc fp sline scol)

tok :: (String -> Token) -> Action
tok f input@(_,_,_,str) len = do
  span <- getSpan input len
  return $ L span (f $ take len str)

mkTok :: SrcSpan -> Token -> Alex (Located Token)
mkTok span token = do
  maybeStartLayout token
  return $ L span token

maybeStartLayout :: Token -> Alex ()
maybeStartLayout TkLet     = pushLexCode layout
maybeStartLayout TkLetB    = pushLexCode layout
maybeStartLayout TkOf      = pushLexCode layout
maybeStartLayout TkDefault = pushLexCode layout
maybeStartLayout _         = return ()


mkPunct :: Action
mkPunct input@(_,_,_,str) len = do
  span <- getSpan input len
  mkTok span =<< case take len str of
    "("  -> return TkLParen
    ")"  -> return TkRParen
    "["  -> return TkLBracket
    "]"  -> return TkRBracket
    ","  -> return TkComma
    "."  -> return TkPeriod
    "|"  -> return TkBar
    "`"  -> return TkBackquote
    "(|" -> return TkLOBracket
    "|)" -> return TkROBracket
    "@"  -> return TkAt
    "\\" -> return TkBackslash
    "::" -> return TkDColon
    "_"  -> return TkUnderscore
    "->" -> return TkLArrow
    p    -> lexError $ "Currently, the special symbol " ++ p ++ " is not supported (reserved for future)."

mkOp :: Action
mkOp input@(_,_,_,str) len = do
  span <- getSpan input len
  mkTok span =<< case take len str of
    "-"  -> return TkMinus
    "+"  -> return TkPlus
    "!"  -> return TkBang
    "="  -> return TkEqual
    "==" -> return TkDEqual
    "<"  -> return TkLess
    ":"  -> return TkColon
    "$"  -> return TkDollar
    op   -> lexError $ "Currently, the operator " ++ op ++ " is not supported (reserved for future)."

mkReserved :: Action
mkReserved input@(_,_,_,str) len = do
  span <- getSpan input len
  mkTok span =<< case take len str of
    "if"    -> return TkIf
    "then"  -> return TkThen
    "else"  -> return TkElse
    "case"  -> return TkCase
    "case*" -> return TkCaseB
    "of"    -> return TkOf
    "let"   -> return TkLet
    "let*"  -> return TkLetB
    "in"    -> return TkIn
    "abort" -> return TkAbort
    "data"  -> return TkData
    "type"  -> return TkType
    "with"  -> return TkWith
    "#include" -> return TkInclude
    "default" -> return TkDefault
    "lift"  -> return TkLift
    "lift_" -> return TkLift_
    "liftInj" -> return TkLiftInj
    "#funs" -> return TkFuns
    "#root" -> return TkRoot
    "#nonRoots" -> return TkNonRoots
    "#examples" -> return TkExamples
    s | "reconciled" `isPrefixOf` s -> return TkReconciledBy
    key ->
      lexError $ "The keyword " ++ key ++ " is not supported now, but is reserved for future."

tokenSequence = do
  t <- alexMonadScan
  case t of
    L _ TkEOF -> return []
    _         -> fmap (t:) tokenSequence


data Token = TkIf
           | TkThen
           | TkElse
           | TkCase
           | TkCaseB
           | TkOf
           | TkLet
           | TkLetB
           | TkIn
           | TkAbort
           | TkData
           | TkType
           | TkWith
           | TkReconciledBy
           | TkDefault
           | TkLift
           | TkLift_
           | TkLiftInj
           | TkInclude
           -- 
           | TkRoot
           | TkNonRoots
           | TkExamples
             --
           | TkEqual
           | TkDEqual
           | TkLess
           | TkColon
           | TkDColon
           | TkLParen
           | TkRParen
           | TkLBrace
           | TkRBrace
           | TkVLBrace
           | TkVRBrace
           | TkLArrow
           | TkLBracket
           | TkRBracket
           | TkBar
           | TkSemicolon
           | TkPlus
           | TkMinus
           | TkBang
           | TkAt
           | TkDollar
           | TkBackslash
           | TkBackquote
           | TkUnderscore
           | TkLOBracket
           | TkROBracket
           | TkPeriod
           | TkComma
           | TkChar   Char
           | TkString String
           | TkVarId  String
           | TkConId  String
           | TkNumber Integer
             --
           | TkEOF
             --
           | TkFuns
           deriving (Eq, Ord, Show)


beginComment :: Action
beginComment _ _ = do
  pushLexCode comment
  alexMonadScan

endComment :: Action
endComment _ _ = do
  _ <- popLexCode
  alexMonadScan


alexEOF = return $ L noSrcSpan TkEOF
}
