{
{- Copyright (c) 2014. Robert Dockins. -}

-- | This module implements the parser for the Orlin language.  It is an
--   LALR(1) parser generated by the Happy parser-generator tool.
module Orlin.Parser where

import Control.Applicative

import Orlin.Tokens
import Orlin.AST
import Orlin.Lexer
}

%tokentype { (Located Token) }
%error { parseError }

%token IDENT { L _ (TIdent _) }
%token LPAREN { L _ LPAREN }
%token RPAREN { L _ RPAREN }
%token LBRACK { L _ LBRACK }
%token RBRACK { L _ RBRACK }
%token LBRACE { L _ LBRACE }
%token RBRACE { L _ RBRACE }
%token LANGLE { L _ LANGLE }
%token RANGLE { L _ RANGLE }

%token SUPERSCRIPT { L _ (SUPERSCRIPT _) }
%token DEFS { L _ DEFS }
%token DOT { L _ DOT }
%token COMMA { L _ COMMA }
%token SEMI { L _ SEMI }
%token BIG_ARROW { L _ BIG_ARROW }
%token SM_ARROW { L _ SM_ARROW }
%token PLUS { L _ PLUS }
%token MINUS { L _ MINUS }
%token HYPHEN { L _ HYPHEN }
%token EQUAL { L _ EQUAL }
%token TOPOWER { L _ TOPOWER }
%token LE { L _ Orlin.Tokens.LE }
%token GE { L _ Orlin.Tokens.GE }
%token LT { L _ Orlin.Tokens.LT }
%token GT { L _ Orlin.Tokens.GT }
%token STAR { L _ STAR }
%token CDOT { L _ CDOT }
%token SLASH { L _ SLASH }
%token NE { L _ NE }
%token COLON { L _ COLON }
%token DCOLON { L _ DCOLON }
%token UNDERSCORE { L _ UNDERSCORE }
%token DEC_NUMBERLIT { L _ (DecNumberLit _) }
%token HEX_NUMBERLIT { L _ (HexNumberLit _) }
%token STRINGLIT { L _ (StringLit _) }
%token SM_LAMBDA { L _ SM_LAMBDA }
%token BIG_LAMBDA { L _ BIG_LAMBDA }

-- keywords
%token MODULE { L _ MODULE }
%token WHERE { L _ WHERE }
%token QUANTITY { L _ QUANTITY }
%token UNIT { L _ UNIT }
%token ALIAS { L _ ALIAS }
%token CONVERSION { L _ CONVERSION }
%token CONSTANT { L _ CONSTANT }
%token PER { L _ PER }
%token SYMBOLIC { L _ SYMBOLIC }
%token PRIMITIVE { L _ PRIMITIVE }
%token FORALL { L _ FORALL }
%token EXISTS { L _ EXISTS }
%token REAL { L _ REAL }
%token INT { L _ INT }
%token NAT { L _ NAT }


%right SM_ARROW
%left COMMA
%left SEMI

%left LE
%left LT
%left GE
%left GT
%left EQUAL
%left NE

-- %right PLUSPLUS

%right PLUS
%left MINUS
%left HYPHEN
%right STAR
%right CDOT
%nonassoc SLASH
-- %nonassoc TILDE

%monad { P }{ thenP }{ returnP }
%lexer { lexer } { L _ EOF }

%name moduleParser module
%name cmdParser cmd

%%

list(p)
   : p COMMA list(p)                     { $1 : $3 }
   | p                                   { $1 : [] }

pnlist(p)
   : p COMMA pnlist(p)                   { (loc $1, $1) : $3 }
   | p                                   { (loc $1, $1) : [] }

ident :: { Ident }
   : IDENT                               { Ident (loc $1) (token_str $1) }

module :: { PreModule }
module
   : MODULE ident WHERE
     LBRACE decl_group RBRACE            { Module $2 $5 }

decl_group :: { [(Pn,PreDecl)] }
   : decl SEMI decl_group                { $1 : $3 }
   |                                     { [] }

expr_atom :: { PreExpr }
   : DEC_NUMBERLIT                       { PExprDecLit (loc $1) (token_str $1) }
   | HEX_NUMBERLIT                       { PExprHexLit (loc $1) (token_str $1) }
   | ident                               { PExprIdent $1 }
   | LPAREN expr RPAREN                  { PExprParens (loc $1) $2 }
   | REAL                                { PExprBase $1 }
   | INT                                 { PExprBase $1 }
   | NAT                                 { PExprBase $1 }


expr_exp :: { PreExpr }
   : expr_atom                           { $1 }
   | expr_atom SUPERSCRIPT               { PExprSuperscript $1 (L (loc $2) (token_str $2)) }
   | expr_atom TOPOWER expr_atom         { PExprBinOp $1 $2 $3 }

expr_unit :: { PreExpr }
   : expr_exp                            { $1 } 
   | expr_exp LANGLE expr RANGLE         { PExprUnit $1 $3 }

expr_app :: { PreExpr }
   : expr_unit                           { $1 }
   | expr_app expr_unit                  { PExprApply $1 $2 }

expr_neg :: { PreExpr }
   : expr_app                            { $1 }
   | HYPHEN expr_exp                     { PExprNeg (loc $1) $2 }

expr_op :: { PreExpr }
   : expr_neg                            { $1 }
   | expr_op PLUS expr_op                { PExprBinOp $1 $2 $3 }
   | expr_op MINUS expr_op               { PExprBinOp $1 $2 $3 }
   | expr_op HYPHEN expr_op              { PExprBinOp $1 $2 $3 }
   | expr_op CDOT expr_op                { PExprBinOp $1 $2 $3 }
   | expr_op STAR expr_op                { PExprBinOp $1 $2 $3 }
   | expr_op SLASH expr_op               { PExprBinOp $1 $2 $3 }
   | expr_op SM_ARROW expr_op            { PExprBinOp $1 $2 $3 }

expr_quantify :: { PreExpr }
   : expr_op                             { $1 }
   | SM_LAMBDA binders
     COMMA expr_quantify                 { PExprQuantify $1 $2 $4 }
   | BIG_LAMBDA binders
     COMMA expr_quantify                 { PExprQuantify $1 $2 $4 }
   | FORALL binders
     COMMA expr_quantify                 { PExprQuantify $1 $2 $4 }
   | EXISTS binders
     COMMA expr_quantify                 { PExprQuantify $1 $2 $4 }

expr :: { PreExpr }
   : expr_quantify                       { $1 }

binders :: { [Binder] }
   :                                     { [] }
   | binder binders                      { ($1:$2) }

binder :: { Binder }
   : ident                               { Binder [$1] Nothing }
   | LPAREN idents RPAREN                { Binder $2 Nothing }
   | LPAREN idents COMMA expr RPAREN     { Binder $2 (Just $4) }

idents :: { [Ident] }
   : ident                               { [$1] }
   | ident idents                        { ($1:$2) }

decl :: { (Pn,PreDecl) }
decl
   : QUANTITY ident                      { (loc $1, QuantityDecl $2) }
   | UNIT ident ident                    { (loc $1, UnitDecl $2 [$3]) }
   | UNIT ident ident ALIAS ident        { (loc $1, UnitDecl $2 [$3,$5]) }
   | UNIT ident DEFS expr                { (loc $1, UnitDefn [$2] $4) }
   | UNIT ident ALIAS ident DEFS expr    { (loc $1, UnitDefn [$2,$4] $6) }
   | CONVERSION expr PER expr            { (loc $1, ConversionDecl $2 $4) }
   | CONSTANT ident DEFS expr            { (loc $1, ConstantDefn [$2] $4) }
   | CONSTANT ident ALIAS ident      
        DEFS expr                        { (loc $1, ConstantDefn [$2,$4] $6) }
   | SYMBOLIC CONSTANT ident
        DEFS expr                        { (loc $1, SymbConstantDefn [$3] $5) }
   | SYMBOLIC CONSTANT ident
        ALIAS ident
        DEFS expr                        { (loc $1, SymbConstantDefn [$3,$5] $7) }
   | PRIMITIVE ident COLON expr          { (loc $1, PrimDecl $2 $4) }
   | ident COLON expr                    { (loc $1, TypeSig $1 $3) }
   | ident DEFS expr                     { (loc $1, Definition $1 $3) }

cmd :: { PreREPLCommand }
   :                                     { DoNothing } 
   | UNIT unifyList                      { UnifyUnits [] $2 }
   | UNIT LBRACE list(ident) RBRACE
        unifyList                        { UnifyUnits $3 $5 }

unifyList :: { [PreExpr] }
unifyList
   : expr EQUAL expr                     { [$1,$3] }
   | expr EQUAL unifyList                { ($1:$3) }

{
data Pushback
 = PushbackNone
 | PushbackTok (Located Token)
 | RememberTok (Located Token)
 deriving (Show)

-- | Parser state record
data ParseState
 = ParseState
   { alex_state    :: AlexState       -- ^ Internal state of the lexer
   , parse_file    :: FilePath        -- ^ Name of the file we are parsing
   , pushback_tok  :: Pushback        -- ^ Remember the last token we got for pushback
   , parse_errors  :: [(Pn, String)]  -- ^ Accumulated list of parse errors
   , lexical_error :: Bool            -- ^ Did the lexer give us an error?
   }
 deriving (Show)

initParseState :: FilePath -> String -> ParseState
initParseState fp input =
  ParseState
  { alex_state    = initAlexState input
  , parse_file    = fp
  , pushback_tok  = PushbackNone
  , parse_errors  = []
  , lexical_error = False
  }

newtype P a = P { unP :: ParseState -> (ParseState, Maybe a) }

thenP m f = P $ \st ->
    let (st', x) = unP m st
     in case x of
          Nothing -> (st', Nothing)
          Just a  -> unP (f a) st'

returnP x = P $ \st -> (st, Just x)

failP msg = P $ \st ->
  let AlexPn _ l c = alex_pos (alex_state st)
      pn = Pn (parse_file st) l c
   in (st{ parse_errors = parse_errors st ++ [(pn, msg)]}, Nothing)

errorP :: Pn -> String -> P a
errorP pn msg = P $ \st -> (st{ parse_errors = parse_errors st ++ [(pn, msg)]}, Nothing)

parseError :: Located Token -> P a
parseError tk = errorP (loc tk) "syntax error"

instance Monad P where
  (>>=) = thenP
  return = returnP
  fail = failP

instance Functor P where
  fmap f m = m >>= return . f

instance Applicative P where
  pure = return
  f <*> x = f >>= \f' -> x >>= \x' -> return (f' x')

instance PMonad P where
  parseFail = errorP


-- | Check to see if we have a pushback token to use; if so, use it immediately.
--   If not, invoke the Alex lexer to produce a new token and do the necessary
--   bookeeping before passing it to our continuation.  Fail if we get a lexical
--   error from the underlying lexer.
--
lexer :: (Located Token -> P a) -> P a
lexer k = P $ \st ->
     case pushback_tok st of

       -- We have a pushback token, use it
       PushbackTok t -> unP (k t) st{ pushback_tok = PushbackNone }

       -- No pushback token, call the lexer
       _ ->
         case unAlex alexMonadScan (alex_state st) of

            -- We got a lexical error; bail out
            Left msg ->
              let fp = parse_file st
                  (AlexPn _ l c)  = alex_pos (alex_state st)
                  st' = st{ parse_errors = parse_errors st ++ [(Pn fp l c, msg)]
                          , lexical_error = True }
               in ( st', Nothing )

            -- We got a token, do bookeeping and enter the continuation
            Right ( ast', (AlexPn _ l c, tok) ) ->
              let fp = parse_file st
                  ltok = L (Pn fp l c) tok
                  st' = st{ alex_state = ast'
                          , pushback_tok = RememberTok ltok }
               in unP (k ltok) st'


-- | Drop tokens until we find a DOT, indicating the end of
--   a declaration, or until we hit end-of-file.
discardTokens :: P a -> P a -> P a
discardTokens meof mdot = lexer (\t ->
   case t of
     (L _ EOF) -> meof
     (L _ DOT) -> mdot
     a -> discardTokens meof mdot)

-- | Mark the last token we got from the lexer to be reused.
pushbackToken :: ParseState -> ParseState
pushbackToken st =
  case pushback_tok st of
     RememberTok tok -> st{ pushback_tok = PushbackTok tok }
     _ -> st

returnToken :: Located Token -> ParseState -> ParseState
returnToken tok st = st{ pushback_tok = PushbackTok tok }


runModuleParser :: FilePath -> String -> Either [(Pn,String)] PreModule
runModuleParser fp str =
   let (st',x) = unP moduleParser (initParseState fp str)
    in case x of
          Nothing -> Left (parse_errors st')
          Just m -> Right m

runCommandParser :: String -> Either [(Pn,String)] PreREPLCommand
runCommandParser str =
  let (st',x) = unP cmdParser (initParseState "" str)
   in case x of
         Nothing -> Left (parse_errors st')
	 Just m -> Right m
}
