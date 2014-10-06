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

data Module unit num = Module Ident [(Pn,Decl unit num)]
 deriving (Eq, Show, Ord)

data PreExpr 
  = PExprNumLit Pn String
  | PExprSuperscript PreExpr (Located String)
  | PExprBinOp PreExpr (Located Token) PreExpr
  | PExprIdent Ident
  | PExprUnit PreExpr PreExpr
  | PExprParens Pn PreExpr
  | PExprNeg Pn PreExpr
  | PExprToPower PreExpr PreExpr
 deriving (Eq, Show, Ord)

instance Loc PreExpr where
  loc (PExprNumLit pn _) = pn
  loc (PExprSuperscript x _) = loc x
  loc (PExprBinOp x _ _) = loc x
  loc (PExprIdent x) = loc x
  loc (PExprParens pn _) = pn
  loc (PExprUnit x _) = loc x
  loc (PExprToPower x _) = loc x

data Number
  = NumLit String
  | NumMult Number Number
  | NumDiv  Number Number
  | NumPlus Number Number
  | NumMinus Number Number
  | NumIdent Ident
  | NumSuper Number String
  | NumUnit Number Unit
 deriving (Eq, Show, Ord)

data Unit
  = UMult Unit Unit
  | UDiv  Unit Unit
  | USuper Unit String
  | UIdent Ident
  | UOne
 deriving (Eq, Show, Ord)

data Decl unit num
  = QuantityDecl Ident
  | UnitDecl Ident [Ident]
  | UnitDefn [Ident] unit
  | ConversionDecl num
  | ConstantDefn [Ident] num
 deriving (Eq, Show, Ord)
