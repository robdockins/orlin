{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module Orlin.AST where

import Prelude hiding (mapM)
import Control.Applicative
import Data.Traversable
import Data.Foldable
import Data.Ratio
import Data.Char

import Orlin.Tokens

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

getIdent :: Ident -> String
getIdent (Ident _ x) = x

data REPLCommandF unit expr
  = DoNothing
  | UnifyUnits [Ident] [unit]
  | UnifyTypes [Ident] [expr]
  | Typecheck expr
 deriving (Eq,Show,Ord)

type PreREPLCommand = REPLCommandF PreExpr PreExpr
type REPLCommand = REPLCommandF (Unit Ident) (Expr Ident)

preREPL2REPL :: PMonad m => PreREPLCommand -> m REPLCommand
preREPL2REPL c =
  case c of
    DoNothing -> return DoNothing
    UnifyUnits is us -> pure (UnifyUnits is) <*> mapM preexprToUnit us
    UnifyTypes is ts -> pure (UnifyTypes is) <*> mapM preexprToExpr ts
    Typecheck e -> fmap Typecheck $ preexprToExpr e

data PreExpr 
  = PExprDecLit Pn String
  | PExprHexLit Pn String
  | PExprSuperscript PreExpr (Located String)
  | PExprBinOp PreExpr (Located Token) PreExpr
  | PExprIdent Ident
  | PExprUnit PreExpr PreExpr
  | PExprParens Pn PreExpr
  | PExprNeg Pn PreExpr
  | PExprApply PreExpr PreExpr
  | PExprBase (Located Token)
  | PExprQuantify (Located Token) [PreBinder] PreExpr
  | PExprUnitKind Pn
  | PExprTypeKind Pn
 deriving (Eq, Show, Ord)

type PreBinder    = BinderF Ident PreExpr
type Binder ident = BinderF ident (Expr ident)

data BinderF ident expr
  = Binder [ident] (Maybe expr)
 deriving (Eq, Show, Ord)

instance Loc PreExpr where
  loc (PExprDecLit pn _) = pn
  loc (PExprHexLit pn _) = pn
  loc (PExprSuperscript x _) = loc x
  loc (PExprBinOp x _ _) = loc x
  loc (PExprIdent x) = loc x
  loc (PExprParens pn _) = pn
  loc (PExprUnit x _) = loc x
  loc (PExprApply x _) = loc x
  loc (PExprNeg pn _) = pn
  loc (PExprBase tok) = loc tok
  loc (PExprQuantify tok _ _) = loc tok
  loc (PExprUnitKind pn) = pn
  loc (PExprTypeKind pn) = pn


data NumF a
  = NumMult a a
  | NumDiv a a
  | NumPlus a a
  | NumMinus a a
  | NumNegate a
  | NumToPower a Int
 deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

data NumLit
  = NumLit Pn (NumF NumLit)
  | NumDec Pn String Rational
  | NumHex Pn String Integer
  | NumZero Pn
 deriving (Eq, Show, Ord)

instance Loc NumLit where
  loc (NumLit pn _) = pn
  loc (NumDec pn _ _) = pn
  loc (NumHex pn _ _) = pn
  loc (NumZero pn) = pn


data Number ident
  = NumberLit NumLit (Unit ident)
  | NumberIdent ident
  | Number Pn (NumF (Number ident))
 deriving (Eq, Show, Ord)

instance Loc ident => Loc (Number ident) where
  loc (NumberLit n _) = loc n
  loc (NumberIdent i) = loc i
  loc (Number pn _) = pn

data Expr ident
  = Expr Pn (ExprF ident (Expr ident))
 deriving (Eq, Show, Ord)

data BaseType unit
  = BaseReal unit
  | BaseNat
  | BaseInt
  | BaseRational
 deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

data Sort
  = SUnit
  | SType
 deriving (Eq, Show, Ord)

data ExprF ident a
  = ExprNumber (NumF a)
  | ExprNumLit NumLit (Unit ident)
  | ExprIdent ident
  | ExprApp a a
  | ExprAbs ident (Maybe a) a
  | ExprArrow a a
  | ExprForall ident (Maybe a) a
  | ExprBase (BaseType (Unit ident))
  | ExprSort Sort
 deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

instance Loc (Expr a) where
  loc (Expr pn _) = pn

data Unit ident
  = UMult (Unit ident) (Unit ident)
  | UDiv (Unit ident) (Unit ident)
  | UToPower (Unit ident) Integer
  | UIdent ident
  | UOne
  | UZero
 deriving (Eq, Show, Ord)

data DeclF ident unit num expr
  = QuantityDecl ident
  | UnitDecl [ident] ident
  | UnitDefn [ident] unit
  | ConversionDecl num num
  | ConstantDefn [ident] num
  | SymbConstantDefn [ident] expr
  | PrimDecl ident expr
  | DefinitionGroup [DefnF ident expr]
 deriving (Eq, Show, Ord)

data ModuleF ident unit num expr
  = Module Ident [(Pn,DeclF ident unit num expr)]
 deriving (Eq, Show, Ord)

type PreDecl    = DeclF Ident PreExpr PreExpr PreExpr
type Decl ident = DeclF ident (Unit ident) (Number ident) (Expr ident)

type PreModule    = ModuleF Ident PreExpr PreExpr PreExpr
type Module ident = ModuleF ident (Unit ident) (Number ident) (Expr ident)

data DefnF ident expr
  = Definition
  { def_name   :: ident
  , def_params :: [BinderF ident expr]
  , def_type   :: Maybe expr
  , def_expr   :: expr
  }
 deriving (Eq, Show, Ord)

type PreDefn    = DefnF Ident PreExpr
type Defn ident = DefnF ident (Expr ident)

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
     (\_ u -> parseFail (loc u) "unit annotations cannot be nested")
     preexprToNumLit
     NumLit
     id


preexprToNumber :: PMonad m => PreExpr -> m (Number Ident)
preexprToNumber =
  preexprToNumF
    (return . NumberIdent)
    (\e u -> do
          e' <- preexprToNumLit e
          u' <- preexprToUnit u
          return (NumberLit e' u'))
    preexprToNumber
    Number
    (\x -> NumberLit x UOne)
    

preexprToNumF
   :: PMonad m
   => (Ident -> m a)
   -> (PreExpr -> PreExpr -> m a)
   -> (PreExpr -> m a)
   -> (Pn -> NumF a -> a)
   -> (NumLit -> a)
   -> PreExpr
   -> m a
preexprToNumF identF unitF subF inF litF e =
  case e of
    PExprDecLit pn lit -> do
         n <- interpFloatLit pn lit
         if n == 0
            then return $ litF $ NumZero pn
            else return $ litF $ NumDec pn lit n
    PExprHexLit pn lit -> do
         n <- interpHexLit pn lit
         if n == 0
            then return $ litF $ NumZero pn
            else return $ litF $ NumHex pn lit n

    PExprSuperscript num (L pn exp) ->
         do num' <- subF num
            exp' <- parseExp pn exp
            return (inF (loc num) $ NumToPower num' (fromIntegral exp'))
    PExprBinOp num (L _ TOPOWER) exp -> do
            num' <- subF num
            exp' <- preexprToExp exp
            return (inF (loc num) $ NumToPower num' (fromIntegral exp'))
    PExprBinOp x op y ->
      do x' <- subF x
         y' <- subF y
         fmap (inF (loc x)) $ parseNumOp op x' y'
    PExprUnit num u -> unitF num u
    PExprIdent i -> identF i
    PExprParens _ x -> preexprToNumF identF unitF subF inF litF x
    PExprNeg pn x -> fmap (inF pn . NumNegate) $ subF x
    _ -> parseFail (loc e) $ unwords ["not a valid numeric value",show e]

foldNumLit :: PMonad m => NumLit -> m Rational
foldNumLit (NumZero _)  = return 0
foldNumLit (NumDec _ _ r) = return r
foldNumLit (NumHex _ _ x) = return $ x%1
foldNumLit (NumLit _ l) =
  case l of
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

unitOp :: PMonad m => Located Token -> Unit Ident -> Unit Ident -> m (Unit Ident)
unitOp (L pn op) x y =
  case op of
    STAR  -> return $ UMult x y
    CDOT  -> return $ UMult x y
    SLASH -> return $ UDiv x y
    _ -> parseFail pn $ unwords ["invalid unit operator:", show op]

preexprToUnit :: PMonad m => PreExpr -> m (Unit Ident)
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
           return $ UToPower u' (fromIntegral exp')
    PExprBinOp u (L _ TOPOWER) exp ->
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


parseExprOp :: PMonad m => Located Token -> Expr Ident -> Expr Ident -> m (Expr Ident)
parseExprOp (L pn tok) x y =
  case tok of
    STAR     -> return $ Expr pn $ ExprNumber $ NumMult x y
    CDOT     -> return $ Expr pn $ ExprNumber $ NumMult x y
    SLASH    -> return $ Expr pn $ ExprNumber $ NumDiv x y
    PLUS     -> return $ Expr pn $ ExprNumber $ NumPlus x y
    MINUS    -> return $ Expr pn $ ExprNumber $ NumMinus x y
    HYPHEN   -> return $ Expr pn $ ExprNumber $ NumMinus x y
    SM_ARROW -> return $ Expr pn $ ExprArrow x y
    _ -> parseFail pn $ unwords ["unknown expression operator", show tok]


preexprToExpr :: PMonad m => PreExpr -> m (Expr Ident)
preexprToExpr e =
  case e of
    PExprParens _ x -> preexprToExpr x

    PExprBase tok ->
       case tok of
         L pn NAT  -> return (Expr pn $ ExprBase BaseNat)
         L pn INT  -> return (Expr pn $ ExprBase BaseInt)
         L pn REAL -> return (Expr pn $ ExprBase $ BaseReal UOne)
         L pn RATIONAL -> return (Expr pn $ ExprBase BaseRational)
         _ -> parseFail (loc tok) $ "invalid expression syntax"

    PExprUnit (PExprBase (L pn REAL)) u ->
         do u' <- preexprToUnit u
            return (Expr pn $ ExprBase $ BaseReal u')

    PExprDecLit pn lit -> do
       n <- interpFloatLit pn lit
       if n == 0
          then return $ Expr pn $ ExprNumLit (NumZero pn) UOne
          else return $ Expr pn $ ExprNumLit (NumDec pn lit n) UOne

    PExprHexLit pn lit -> do
       n <- interpHexLit pn lit
       if n == 0
          then return $ Expr pn $ ExprNumLit (NumZero pn) UOne
          else return $ Expr pn $ ExprNumLit (NumHex pn lit n) UOne

    PExprSuperscript e (L pn exp) ->
         do e' <- preexprToExpr e
            exp' <- parseExp pn exp
            return (Expr (loc e) $ ExprNumber $ NumToPower e' (fromIntegral exp'))
    PExprBinOp e1 (L _ TOPOWER) e2 ->
       do e1' <- preexprToExpr e1
          n <- preexprToExp e2
          return (Expr (loc e1) $ ExprNumber $ NumToPower e1' (fromIntegral n))
    PExprBinOp e1 op e2 ->
       do e1' <- preexprToExpr e1
          e2' <- preexprToExpr e2
          parseExprOp op e1' e2'
    PExprIdent i -> return (Expr (loc i) $ ExprIdent i)
    PExprUnit n u -> 
       do n' <- preexprToNumLit n
          u' <- preexprToUnit u
          return (Expr (loc n) $ ExprNumLit n' u')
    PExprNeg pn x -> fmap (Expr pn . ExprNumber . NumNegate) $ preexprToExpr x
    PExprApply x y ->
       do x' <- preexprToExpr x
          y' <- preexprToExpr y
          return (Expr (loc x) $ ExprApp x' y')
    PExprQuantify tok bs e -> preexprToExpr e >>= unwindExprBinders tok bs

    PExprUnitKind pn -> return $ Expr pn $ ExprSort $ SUnit
    PExprTypeKind pn -> return $ Expr pn $ ExprSort $ SType


unwindExprBinders :: PMonad m => Located Token -> [PreBinder] -> Expr Ident -> m (Expr Ident)
unwindExprBinders (L pn tok) bs0 e0 =
  case tok of
    SM_LAMBDA -> unwind ExprAbs    bs0
    FORALL    -> unwind ExprForall bs0 
    _ -> parseFail pn $ unwords ["binder not allowed in expressions:", show tok]
 
 where unwind _ [] = return e0
       unwind f (Binder is mt : bs) =
            do e <- unwind f bs
               mt' <- maybe (return Nothing) (fmap Just . preexprToExpr) mt
               return $ unwind_is f is mt' e

       unwind_is _ [] _ e = e
       unwind_is f (i:is) mt e = Expr (loc i) $ f i mt (unwind_is f is mt e)


predeclToDecl :: PMonad m => PreDecl -> m (Decl Ident)
predeclToDecl d =
  case d of
    QuantityDecl i -> return $ QuantityDecl i
    UnitDecl is i -> return $ UnitDecl is i
    UnitDefn is u -> fmap (UnitDefn is) $ preexprToUnit u
    ConversionDecl n1 n2 -> pure ConversionDecl <*> preexprToNumber n1 <*> preexprToNumber n2
    ConstantDefn is n -> fmap (ConstantDefn is) $ preexprToNumber n
    SymbConstantDefn is e -> fmap (SymbConstantDefn is) $ preexprToExpr e
    PrimDecl id ty -> fmap (PrimDecl id) (preexprToExpr ty)
    DefinitionGroup defs -> fmap DefinitionGroup $ mapM predefnToDefn defs
    
prebinderToBinder :: PMonad m => PreBinder -> m (Binder Ident)
prebinderToBinder (Binder is x) =
   fmap (Binder is) $ maybe (return Nothing) (fmap Just . preexprToExpr) x

predefnToDefn :: PMonad m => PreDefn -> m (Defn Ident)
predefnToDefn (Definition id pms typ exp) =
  do pms' <- mapM prebinderToBinder pms
     typ' <- traverse preexprToExpr typ
     exp' <- preexprToExpr exp
     return (Definition id pms' typ' exp')          

premoduleToModule :: PMonad m => PreModule -> m (Module Ident)
premoduleToModule (Module i ds) = fmap (Module i) (mapM f ds)
  where f (n,d) = predeclToDecl d >>= \d' -> return (n,d')
