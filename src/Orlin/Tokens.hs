{- Copyright (c) 2014. Robert Dockins. -}

-- | This module defines the set of tokens produced by the lexer
--   and consumed by the parser.
module Orlin.Tokens where

-- | A 'Pn' indicates a position in a source file.
--   It contains the name of the source file, the line number and column number.
data Pn = Pn FilePath !Int !Int
  deriving (Eq, Ord, Show)

-- | Display a position in the format 'filename:line:col:'
--   for printing error messages.
displayPn :: Pn -> String
displayPn (Pn f l c) = f ++ ":" ++ show l ++ ":" ++ show c ++ ": "

-- | @Located a@ represents an element of type @a@ paired with a location.
data Located a = L Pn a
  deriving (Show, Eq, Ord)

-- | Retrieve the element from a 'Located' package.
unloc :: Located a -> a
unloc (L _ x) = x

-- | The main token datatype.
data Token
  = LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | LDATA
  | RDATA
  | LANGLE
  | RANGLE
  | CDOT
  | SUPERSCRIPT String
  | FORALL
  | EXISTS
  | DEFS
  | DOT
  | COMMA
  | SEMI
  | TIdent String
  | DecNumberLit String
  | HexNumberLit String
  | StringLit String
  | DCOLON
  | COLON
  | LBRACE
  | RBRACE
  | BIG_ARROW
  | SM_ARROW
  | BIG_LAMBDA
  | SM_LAMBDA
  | PLUS
  | HYPHEN
  | MINUS
  | EQUAL
  | PARTIAL
  | LE
  | GE
  | LT
  | GT
  | NE
  | STAR
  | SLASH
  | TOPOWER
  | UNDERSCORE
  | EOF

  -- Keywords
  | MODULE
  | WHERE
  | QUANTITY
  | UNIT
  | ALIAS
  | CONVERSION
  | CONSTANT
  | PER
  | SYMBOLIC
  | REAL
  | INT
  | NAT
  | RATIONAL
  | PRIMITIVE
  | TYPE
  | OF
  | DEFINITION
  | WITH
 deriving (Eq,Show,Ord)


-- | Given a string, this function determines if the string
--   represents a keyword.  If so, it returns the corresponding
--   token.  Otherwise, it return an identifier token containing
--   the given string.
--
keyword_or_ident :: String -> Token
keyword_or_ident "module"     = MODULE
keyword_or_ident "where"      = WHERE
keyword_or_ident "quantity"   = QUANTITY
keyword_or_ident "unit"       = UNIT
keyword_or_ident "alias"      = ALIAS
keyword_or_ident "conversion" = CONVERSION
keyword_or_ident "constant"   = CONSTANT
keyword_or_ident "per"        = PER
keyword_or_ident "forall"     = FORALL
keyword_or_ident "exists"     = EXISTS
keyword_or_ident "symbolic"   = SYMBOLIC
keyword_or_ident "real"       = REAL
keyword_or_ident "nat"        = NAT
keyword_or_ident "int"        = INT
keyword_or_ident "rational"   = RATIONAL
keyword_or_ident "primitive"  = PRIMITIVE
keyword_or_ident "type"       = TYPE
keyword_or_ident "of"         = OF
keyword_or_ident "definition" = DEFINITION
keyword_or_ident "with"       = WITH

keyword_or_ident s            = TIdent s


-- | Extract a string from a token.  Fails if the token is not
--   one of 'TIdent', 'Var', 'NumberLit' or 'StringLit'.
--
token_str :: Located Token -> String
token_str (L _ (TIdent x)) = x
token_str (L _ (DecNumberLit x)) = x
token_str (L _ (HexNumberLit x)) = x
token_str (L _ (StringLit x)) = x
token_str (L _ (SUPERSCRIPT x)) = x
token_str (L _ t) = error $ show t ++ " does not contain a string"
