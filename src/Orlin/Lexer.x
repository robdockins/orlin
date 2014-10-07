{
{-# LANGUAGE StandaloneDeriving #-}
{- Copyright (c) 2014. Robert Dockins. -}

module Orlin.Lexer
( alexMonadScan
, AlexState(..)
, Alex(..)
, AlexPosn(..)
, runlexer
, initAlexState
, docStrings
) where

import Prelude hiding (LT, GT)
import Control.Monad (when)
import Data.Char

import Orlin.Tokens
}

%wrapper "monadUserState"

$digit = [0-9]
$alpha = [A-Z a-z]
$lower = [a-z]
$upper = [A-Z]
$hexdigit = [$digit a-f A-F]
$superscript = [⁰¹²³⁴⁵⁶⁷⁸⁹⁻⁺]
$subscript   = [₀₁₂₃₄₅₆₇₈₉ₐₑᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ]
$lgreek      = [αβγδεζηθικλμνξοπρστυφχψω]
$ugreek      = [ΑΒΓΔΕΖΗΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ]
$extra       = [ℏƛℓ]

@sign        = ("-"|"+")?
@positive    = [$digit] [$digit _]*
@float       = @positive "." @positive
@exponent    = ("e" | "E") @sign @positive
@scientific  = (@positive | @float) @exponent
@floatlit    = @float
@int         = @positive
@hex         = "0x" [$hexdigit] [$hexdigit _]+
@ident       = [$alpha $lgreek $ugreek $extra]
               [$alpha $digit \_ $subscript $lgreek $ugreek $extra ' ]*  

tokens :-

<string> \\\"                        { litstringsegment "\"" }
<string> \\\'                        { litstringsegment "\'" }
<string> \\\\                        { litstringsegment "\\" }
<string> \\n                         { litstringsegment "\n" }
<string> \\a                         { litstringsegment "\a" }
<string> \\b                         { litstringsegment "\b" }
<string> \\f                         { litstringsegment "\f" }
<string> \\r                         { litstringsegment "\r" }
<string> \\t                         { litstringsegment "\t" }
<string> \\v                         { litstringsegment "\v" }
<string> \\ (u)+ [$hexdigit]{4}      { hexchar }
<string> [$white $printable]#[\\\"]+ { stringsegment }
<string> \"                          { endString }

<0>  \"                              { startString }
<0>  ^ "--" ("-")+ .* $              { docString }
<0>  [$white]+                       { skipSpace }
<0>  "--".*                          { skipSpace }
<0>  "–".*                          { skipSpace }
<0>  @ident                          { emits keyword_or_ident }
<0>  @scientific                     { emits DecNumberLit }
<0>  @floatlit                       { emits DecNumberLit }
<0>  @int                            { emits DecNumberLit }
<0>  @hex                            { emits HexNumberLit }
<0>  $superscript+                   { emits SUPERSCRIPT }
<0>  "∀"                            { emit FORALL }
<0>  "∃"                            { emit EXISTS }
<0>  "→"                            { emit SM_ARROW }
<0>  "⇒"                            { emit BIG_ARROW }
<0>  "<|"                           { emit LANGLE }
<0>  "|>"                           { emit RANGLE }
<0>  "〈"                             { emit LANGLE }
<0>  "〉"                             { emit RANGLE }
<0>  "<<"                            { emit LDATA }
<0>  ">>"                            { emit RDATA }
<0>  "《"                            { emit LDATA }
<0>  "》"                            { emit RDATA }
<0>  "("                             { emit LPAREN }
<0>  ")"                             { emit RPAREN }
<0>  "["                             { emit LBRACK }
<0>  "]"                             { emit RBRACK }
<0>  "."                             { emit DOT }
<0>  "·"                             { emit CDOT }
<0>  ":="                            { emit DEFS }
<0>  "≙"                             { emit DEFS }
<0>  ","                             { emit COMMA }
<0>  ";"                             { emit SEMI }
<0>  "->"                            { emit SM_ARROW }
<0>  "=>"                            { emit BIG_ARROW }
<0>  "+"                             { emit PLUS }
<0>  "−"                             { emit MINUS }
<0>  "-"                             { emit HYPHEN }
<0>  "="                             { emit EQUAL }
<0>  "*"                             { emit STAR }
<0>  "^"                             { emit TOPOWER }
<0>  "/"                             { emit SLASH }
<0>  "<>"                            { emit NE }
<0>  "!="                            { emit NE }
<0>  "≠"                             { emit NE }
<0>  "<="                            { emit LE }
<0>  "=<"                            { emit LE }
<0>  ">="                            { emit GE }
<0>  "≤"                             { emit LE }
<0>  "≥"                             { emit GE }
<0>  "<"                             { emit LT }
<0>  ">"                             { emit GT }
<0>  "_"                             { emit UNDERSCORE }
<0>  "{"                             { emit LBRACE }
<0>  "}"                             { emit RBRACE }
<0>  "::"                            { emit DCOLON }
<0>  ":"                             { emit COLON }
<0>  "\"                            { emit SM_LAMBDA }
<0>  "𝛌"                             { emit SM_LAMBDA }
<0>  "/\"                           { emit BIG_LAMBDA }
<0>  "𝚲"                             { emit BIG_LAMBDA }

-- <0>  "∂"                             { emit PARTIAL }



{
-- | The user-defined lexer state.  It contains: the starting position
--   of the current token; a partially-accumulated string literal, if
--   the lexer is in the string-scanning mode; and a list of found
--   documentation strings.
type AlexUserState = (AlexPosn,String,[(AlexPosn,String)])
alexInitUserState = (AlexPn 0 1 1, "", [])

-- | Skip whitespace, remember our current position as the start
--   of the next token.
skipSpace :: AlexAction (AlexPosn,Token)
skipSpace _ _ = resetPosn >> alexMonadScan

getPosn :: Alex AlexPosn
getPosn = do
  (pn,_,_) <- alexGetUser
  return pn

resetPosn :: Alex ()
resetPosn = do
  (pn,_,_,_) <- alexGetInput
  setPosn pn

stringsegment :: AlexAction (AlexPosn,Token)
stringsegment (_,_,_,str) len = do
   rememberstring (take len str)
   alexMonadScan

litstringsegment :: String -> AlexAction (AlexPosn,Token)
litstringsegment s _ _ = do
   rememberstring s
   alexMonadScan

docString :: AlexAction (AlexPosn,Token)
docString (_,_,_,str) len = do
   rememberdoc (take len str)
   resetPosn
   alexMonadScan

hexchar :: AlexAction (AlexPosn, Token)
hexchar (_,_,_,str) len = do
   let hs = take len str
   rememberstring [decodeChar hs]   
   alexMonadScan

decodeChar :: String -> Char
decodeChar ('\\':s) = decodeChar s
decodeChar ('u':s)  = decodeChar s
decodeChar s = chr $ f 0 s
 where f n [] = n
       f n (x:xs) = f ((n * 16) + digitToInt x) xs

rememberstring :: String -> Alex ()
rememberstring str = do
   (pn,x,ds) <- alexGetUser
   alexSetUser (pn, x ++ str,ds)

rememberdoc :: String -> Alex ()
rememberdoc str = do
   (pn,x,ds) <- alexGetUser
   alexSetUser(pn,x,ds++[(pn,str)])

-- | Emit a specific token
emit :: Token -> AlexAction (AlexPosn,Token)
emit t _ _ = do
   pn <- getPosn
   resetPosn
   return (pn,t)

-- | Emit a token that carries a string argument
emits :: (String -> Token) -> AlexAction (AlexPosn,Token)
emits t (_,_,_,str) len = do
   pn <- getPosn
   resetPosn
   return (pn,t (take len str))

startString :: AlexAction (AlexPosn,Token)
startString _ _ = do
   alexSetStartCode string
   alexMonadScan

endString :: AlexAction (AlexPosn,Token)
endString _ _ = do
   alexSetStartCode 0
   (pn,str,ds) <- alexGetUser
   alexSetUser(pn,"",ds)
   resetPosn
   return (pn,StringLit str)

setPosn :: AlexPosn -> Alex ()
setPosn pn = do
   (_,str,ds) <- alexGetUser
   alexSetUser (pn,str,ds)

alexGetUser :: Alex AlexUserState
alexGetUser = Alex $ \s -> Right (s, alex_ust s)

alexSetUser :: AlexUserState -> Alex ()
alexSetUser u = Alex $ \s -> Right (s{ alex_ust = u} , ())

alexEOF :: Alex (AlexPosn,Token)
alexEOF = do
  sc <- alexGetStartCode
  (p,_,_) <- alexGetUser
  when (sc == string) (alexError "unterminated string literal")
  return (p,EOF)

-- | Initialize the parser with the given input string.
initAlexState :: String -> AlexState
initAlexState input = 
  AlexState {alex_pos = alexStartPos,
             alex_inp = input,
             alex_chr = '\n',
             alex_bytes = [],
             alex_ust = alexInitUserState,
             alex_scd = 0}

-- | Extract any documentation strings found in the input.
docStrings :: AlexState -> [(AlexPosn,String)]
docStrings st = let (_,_,ds) = alex_ust st in ds

-- | Testing procedure that generates a list of tokens from a string input.
runlexer :: String -> [(AlexPosn,Token)]
runlexer str = go (AlexState alexStartPos str '\n' [] 0 alexInitUserState)
  where go st =
          case unAlex alexMonadScan st of
	        Left msg -> error msg
		Right (st',(_,EOF)) -> []
		Right (st',tok) -> tok : go st'

deriving instance Show AlexState
}
