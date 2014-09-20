module Orlin.AST where

import Orlin.Tokens
import Orlin.Lexer

class (Functor m, Monad m) => PTMonad m where
  parseFail :: Pn -> String -> m a

class Loc a where
  loc :: a -> Pn

instance Loc (Located a) where
  loc (L pn _) = pn

instance Loc Ident where
  loc (Ident pn _) = pn

data Ident = Ident Pn String
 deriving (Eq, Show, Ord)

data UIdent = UIdent Pn String
 deriving (Eq, Show, Ord)

data Module = Module UIdent [(Pn,Decl)]
 deriving (Eq, Show, Ord)

data Decl
  = QuantityDecl Ident
  | UnitDecl Ident Ident
 deriving (Eq, Show, Ord)
