{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Orlin.AST where

import Control.Applicative
import Control.Monad
import Data.Ratio
import Data.Char

import Orlin.Tokens
import Orlin.Lexer

class (Functor m, Applicative m, Monad m) => PMonad m where
  parseFail :: Pn -> String -> m a

class Loc a where
  loc :: a -> Pn

instance Loc (Located a) where
  loc (L pn _) = pn

instance Loc Ident where
  loc (Ident pn _) = pn

data Ident = Ident Pn String
 deriving (Eq, Show, Ord)

data Module unit num expr = Module Ident [(Pn,Decl unit num expr)]
 deriving (Eq, Show, Ord)

data PreExpr 
  = PExprDecLit Pn String
  | PExprHexLit Pn String
  | PExprSuperscript PreExpr (Located String)
  | PExprBinOp PreExpr (Located Token) PreExpr
  | PExprIdent Ident
  | PExprUnit PreExpr PreExpr
  | PExprParens Pn PreExpr
  | PExprNeg Pn PreExpr
  | PExprToPower PreExpr PreExpr
  | PExprApply PreExpr PreExpr
 deriving (Eq, Show, Ord)

instance Loc PreExpr where
  loc (PExprDecLit pn _) = pn
  loc (PExprHexLit pn _) = pn
  loc (PExprSuperscript x _) = loc x
  loc (PExprBinOp x _ _) = loc x
  loc (PExprIdent x) = loc x
  loc (PExprParens pn _) = pn
  loc (PExprUnit x _) = loc x
  loc (PExprToPower x _) = loc x
  loc (PExprApply x _) = loc x

data NumF a
  = NumZero
  | NumDec String Rational
  | NumHex String Integer
  | NumMult a a
  | NumDiv a a
  | NumPlus a a
  | NumMinus a a
  | NumNegate a
  | NumToPower a Integer
 deriving (Eq, Show, Ord)


data NumLit = NumLit Pn (NumF NumLit)
 deriving (Eq, Show, Ord)

instance Loc NumLit where
  loc (NumLit pn _) = pn

data Number
  = NumberLit NumLit Unit
  | NumberIdent Ident
  | Number Pn (NumF Number)
 deriving (Eq, Show, Ord)

instance Loc Number where
  loc (NumberLit n u) = loc n
  loc (NumberIdent i) = loc i
  loc (Number pn _) = pn

data Unit
  = UMult Unit Unit
  | UDiv Unit Unit
  | UToPower Unit Integer
  | UIdent Ident
  | UOne
  | UZero
 deriving (Eq, Show, Ord)

data Decl unit num expr
  = QuantityDecl Ident
  | UnitDecl Ident [Ident]
  | UnitDefn [Ident] unit
  | ConversionDecl num num
  | ConstantDefn [Ident] num
  | SymbConstantDefn [Ident] expr
 deriving (Eq, Show, Ord)


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
              '⁰' -> return 0
              '¹' -> return 1
              '²' -> return 2
              '³' -> return 3
              '⁴' -> return 4
              '⁵' -> return 5
              '⁶' -> return 6
              '⁷' -> return 7
              '⁸' -> return 8
              '⁹' -> return 9
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
interpHexLit pn = f 0 . map toLower
 where f !x [] = return x
       f !x ('_':cs) = f x cs
       f !x (c:cs) = do
            d <- interpHexDigit pn c
            f (x*16 + d) cs

parseExp :: PMonad m => Pn -> String -> m Integer
parseExp pn = go
  where go ('-':cs) = fmap (\x -> -x) $ f 0 cs
        go ('+':cs) = f 0 cs
        go ('⁻':cs) = fmap (\x -> -x) $ f 0 cs
        go ('⁺':cs) = f 0 cs
        go cs = f 0 cs

        f !exp [] = return exp
        f !exp (c:cs) = interpDigit pn c >>= \d -> f (10 * exp + d) cs

pow10 :: Integer -> Integer
pow10 !n 
  | n <= 0    = 1
  | otherwise = 10 * pow10 (n-1)

interpFloatLit :: forall m. PMonad m => Pn -> String -> m Rational
interpFloatLit pn = interpInt 0 . map toLower
 where interpInt :: Integer -> String -> m Rational 
       interpInt !x [] = return (x % 1)
       interpInt !x ('_':cs) = interpInt x cs
       interpInt !x ('.':cs) = interpFloat x 0 1 cs
       interpInt !x ('e':cs) = interpExp (x%1) cs
       interpInt !x (c:cs) = 
                do d <- interpDigit pn c
                   interpInt (x * 10 + d) cs
       
       interpFloat :: Integer -> Integer -> Integer -> String -> m Rational
       interpFloat !x !num !denom [] = return ((x%1) + (num%denom))
       interpFloat !x !num !denom ('_':cs) = interpFloat x num denom cs
       interpFloat !x !num !denom ('e':cs) = interpExp ((x%1) + (num%denom)) cs
       interpFloat !x !num !denom (c:cs) =
                do d <- interpDigit pn c
                   interpFloat x (num*10 + d) (denom * 10) cs

       interpExp :: Rational -> String -> m Rational
       interpExp !x cs = 
           do exp <- parseExp pn cs
              if exp < 0
                 then return (x * (1 % (pow10 (-exp))))
                 else return (x * (pow10 exp % 1))

preexprToExp :: PMonad m => PreExpr -> m Integer
preexprToExp e = do
   num' <- foldNumLit =<< preexprToNumLit e
   if denominator num' == 1 
      then return (numerator num')
      else parseFail (loc e) $ "can only raise to integer powers"

parseNumOp :: PMonad m => Located Token -> a -> a -> m (NumF a)
parseNumOp (L pn tok) x y = 
  case tok of
    STAR -> return $ NumMult x y
    CDOT -> return $ NumMult x y
    SLASH -> return $ NumDiv x y
    PLUS -> return $ NumPlus x y
    MINUS -> return $ NumMinus x y
    HYPHEN -> return $ NumMinus x y
    _ -> parseFail pn $ unwords ["unknown numeric binary operator", show tok]

preexprToNumLit :: PMonad m => PreExpr -> m NumLit
preexprToNumLit =
  preexprToNumF
     (\i -> parseFail (loc i) "identifiers not allowed in literals (likely cause: misplaced unit annotation)")
     (\n u -> parseFail (loc u) "unit annotations cannot be nested")
     preexprToNumLit
     NumLit


preexprToNumber :: PMonad m => PreExpr -> m Number
preexprToNumber =
  preexprToNumF
    (return . NumberIdent)
    (\e u -> do
          e' <- preexprToNumLit e
          u' <- preexprToUnit u
          return (NumberLit e' u'))
    preexprToNumber
    Number

preexprToNumF
   :: PMonad m
   => (Ident -> m a)
   -> (PreExpr -> PreExpr -> m a)
   -> (PreExpr -> m a)
   -> (Pn -> NumF a -> a)
   -> PreExpr
   -> m a
preexprToNumF identF unitF subF inF e =
  case e of
    PExprDecLit pn lit -> fmap (inF pn . NumDec lit) $ interpFloatLit pn lit
    PExprHexLit pn lit -> fmap (inF pn . NumHex lit) $ interpHexLit pn lit

    PExprSuperscript num (L pn exp) ->
         do num' <- subF num
            exp' <- parseExp pn exp
            return (inF (loc num) $ NumToPower num' exp')
    PExprBinOp x op y ->
      do x' <- subF x
         y' <- subF y
         fmap (inF (loc x)) $ parseNumOp op x' y'
    PExprUnit num u -> unitF num u
    PExprIdent i -> identF i
    PExprParens _ x -> preexprToNumF identF unitF subF inF x
    PExprNeg pn x -> fmap (inF pn . NumNegate) $ subF x
    PExprToPower num exp -> do
            num' <- subF num
            exp' <- preexprToExp exp
            return (inF (loc num) $ NumToPower num' exp')

foldNumLit :: PMonad m => NumLit -> m Rational
foldNumLit (NumLit _ l) =
  case l of
    NumZero -> return 0
    NumDec _ r -> return r
    NumHex _ x -> return $ x%1
    NumMult x y  -> pure (*) <*> foldNumLit x <*> foldNumLit y
    NumPlus x y  -> pure (+) <*> foldNumLit x <*> foldNumLit y
    NumMinus x y -> pure (-) <*> foldNumLit x <*> foldNumLit y
    NumNegate x -> fmap negate $ foldNumLit x
    NumToPower x exp -> fmap (^exp) $ foldNumLit x
    NumDiv x y ->
        do x' <- foldNumLit x
           y' <- foldNumLit y
           if y' == 0
              then parseFail (loc y) "Division by zero in a numeric literal"
              else return (x' / y')

unitOp :: PMonad m => Located Token -> Unit -> Unit -> m Unit
unitOp (L pn op) x y =
  case op of
    STAR  -> return $ UMult x y
    CDOT  -> return $ UMult x y
    SLASH -> return $ UDiv x y
    _ -> parseFail pn $ unwords ["invalid unit operator:", show op]

preexprToUnit :: PMonad m => PreExpr -> m Unit
preexprToUnit e =
  case e of
    PExprDecLit pn lit -> 
       do l <- interpFloatLit pn lit
          if l == 1%1
             then return UOne
             else parseFail pn "Invalid unit: named unit or the constant '1' expected"
    PExprIdent i -> return (UIdent i)
    PExprParens _ x -> preexprToUnit x
    PExprSuperscript u (L pn exp) ->
        do u' <- preexprToUnit u
           exp' <- parseExp pn exp
           return $ UToPower u' exp'
    PExprToPower u exp ->
        do u' <- preexprToUnit u
           exp' <- foldNumLit =<< preexprToNumLit exp
           if denominator exp' == 1
              then return $ UToPower u' (numerator exp')
              else parseFail (loc exp) $ "units can only be raised to integer powers"
    PExprBinOp x op y ->
        do x' <- preexprToUnit x
           y' <- preexprToUnit y
           unitOp op x' y'

    _ -> parseFail (loc e) $ unwords ["invalid unit:", show e]

predeclToDecl :: PMonad m => Decl PreExpr PreExpr PreExpr -> m (Decl Unit Number PreExpr)
predeclToDecl d =
  case d of
    QuantityDecl i -> return $ QuantityDecl i
    UnitDecl i is -> return $ UnitDecl i is
    UnitDefn is u -> fmap (UnitDefn is) $ preexprToUnit u
    ConversionDecl n1 n2 -> pure ConversionDecl <*> preexprToNumber n1 <*> preexprToNumber n2
    ConstantDefn is n -> fmap (ConstantDefn is) $ preexprToNumber n
    SymbConstantDefn is e -> return (SymbConstantDefn is e)

premoduleToModule :: PMonad m => Module PreExpr PreExpr PreExpr
                              -> m (Module Unit Number PreExpr)
premoduleToModule (Module i ds) = fmap (Module i) (mapM f ds)
  where f (n,d) = predeclToDecl d >>= \d' -> return (n,d')
