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
  = NumLit Rational
  | NumMult Number Number
  | NumDiv  Number Number
  | NumPlus Number Number
  | NumMinus Number Number
  | NumIdent Ident
  | NumSuper Number Integer
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


class PMonad m where
  parseFail :: Pn -> String -> m ()

interpDigit :: PMonad m => Pn -> Char -> m Integer
interpDigit pn c =
         case c of
              '0' -> return 0
              '1' -> return 1
              '2' -> return 2
              '3' -> return 3
              '4' -> return 4
              '5' -> return 5
              '6' -> return 6
              '7' -> return 7
              '8' -> return 8
              '9' -> return 9
              _ -> parseFail pn $ unwords ["impossible decimal digit:",c:[]]

interpHexDigit :: PMonad m => Pn -> Char -> m Integer
interpHexDigit pn c =
         case c of
              '0' -> return 0
              '1' -> return 1
              '2' -> return 2
              '3' -> return 3
              '4' -> return 4
              '5' -> return 5
              '6' -> return 6
              '7' -> return 7
              '8' -> return 8
              '9' -> return 9
              'a' -> return 10
              'b' -> return 11
              'c' -> return 12
              'd' -> return 13
              'e' -> return 14
              'f' -> return 15
              _ -> parseFail pn $ unwords ["impossible hex digit:",c:[]]

interpHexLit :: PMonad m => Pn -> String -> m Integer
interpHexLit pn = f 0
 where f !x [] = return x
       f !x ('_':cs) = f x cs
       f !x (c:cs) = do
            d <- nterpHexDigit pn c
            f (x*16 + d) cs

interpFloatLit :: PMonad m => Pn -> String -> m Rational
interpFloatLit pn = start 0
 where interpInt !x [] = return (x % 1)
       interpInt !x ('_':cs) = interpInt x cs
       interpInt !x ('.':cs) = interpFloat x 0 1 cs
       interpInt !x (c:cs) = 
                do d <- interpDigit pn c
                   interpInt (x * 10 + d) cs
       
       interpFloat !x !num !denom [] = return (x%1 + num%denom)
       interpFloat !x !num !denom ('_':cs) = interpFloat x num denom cs
       interpFloat !x !num !denom ('e':cs) = interpExp (x%1 + num%denom) cs
       interpFloat !x !num !denom (c:cs) =
                do d <- interpDigit pn c
                   interpFloat x (num*10 + d) (denom * 10) cs

       interpExp !x [] = parseFail pn "empty exponent in scientific literal"
       interpExp !x ('-':cs) = parseExp 0 cs >>= \exp -> x * (1 % pow10 exp)
       interpExp !x ('+':cs) = parseExp 0 cs >>= \exp -> x * (pow10 exp % 1)
       interpExp !x cs       = parseExp 0 cs >>= \exp -> x * (pow10 exp % 1)

       parseExp !exp [] = exp 
       parseExp !exp (c:cs) = interpDigit pn c >>= \d -> parseExp (10*x + d) cs

       pow10 !n 
          | n <= 0    = 1
          | otherwise = 10 * pow10 (n-1)

interpNumLit :: PMonad m => String -> m Rational
interpNumLit '0':'x':str = fmap (% 1) (interpHexLit (toLower str))
interpNumLit str = interpFloatLit 0 str

preexprToUnit :: PMonad m => PreExpr -> m Unit
preexprToUnit e =
  case e of
    PExprNumLit pn lit -> 
       do l <- interpFloatLit pn lit
          if l == 1%1
             then return UOne
             else parseFail pn "Invalid unit: named unit or the constant '1' expected"
    PExprIdent i -> return (UIdent i)
    PExprParens _ x -> preexprToUnit x
    _ -> parseFail (loc e) $ unwords ["invalid unit:", show e]
