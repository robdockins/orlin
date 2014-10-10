{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Orlin.AST where

import Control.Applicative
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

data REPLCommandF unit typ expr
  = DoNothing
  | UnifyUnits [Ident] [unit]
  | UnifyTypes [Ident] [typ]
  | Typecheck expr
 deriving (Eq,Show,Ord)

type PreREPLCommand = REPLCommandF PreExpr PreExpr PreExpr
type REPLCommand = REPLCommandF Unit Type (Expr ())

preREPL2REPL :: PMonad m => PreREPLCommand -> m REPLCommand
preREPL2REPL c =
  case c of
    DoNothing -> return DoNothing
    UnifyUnits is us -> pure (UnifyUnits is) <*> mapM preexprToUnit us
    UnifyTypes is ts -> pure (UnifyTypes is) <*> mapM preexprToType ts
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
  | PExprQuantify (Located Token) [Binder] PreExpr
  | PExprUnitKind Pn
 deriving (Eq, Show, Ord)

data Binder
  = Binder [Ident] (Maybe PreExpr)
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

data NumF a
  = NumZero
  | NumDec String Rational
  | NumHex String Integer
  | NumMult a a
  | NumDiv a a
  | NumPlus a a
  | NumMinus a a
  | NumNegate a
  | NumToPower a Int
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
  loc (NumberLit n _) = loc n
  loc (NumberIdent i) = loc i
  loc (Number pn _) = pn

data Expr ty
  = Expr Pn ty (ExprF (Expr ty))
 deriving (Eq, Show, Ord)

data ExprF a
  = ExprNumber (NumF a)
  | ExprToPower a a
  | ExprNumLit NumLit Unit
  | ExprIdent Ident
  | ExprApp a a
  | ExprAbs Ident (Maybe Type) a
  | ExprTAbs Ident a
  | ExprUAbs Ident a
 deriving (Eq, Show, Ord)

instance Loc (Expr a) where
  loc (Expr pn _ _) = pn

data Unit
  = UMult Unit Unit
  | UDiv Unit Unit
  | UToPower Unit Integer
  | UIdent Ident
  | UOne
  | UZero
 deriving (Eq, Show, Ord)

data Type
  = Type Pn (TypeF Unit Type)
 deriving (Eq, Show, Ord)

data TypeF unit a 
  = TyInt
  | TyNat
  | TyReal unit
  | TyIdent Ident
  | TyArrow a a
  | TyUForall Ident a
 deriving (Eq, Show, Ord)

instance Loc Type where
  loc (Type pn _) = pn

data DeclF unit num typ expr
  = QuantityDecl Ident
  | UnitDecl Ident [Ident]
  | UnitDefn [Ident] unit
  | ConversionDecl num num
  | ConstantDefn [Ident] num
  | SymbConstantDefn [Ident] expr
  | PrimDecl Ident typ
  | TypeSig Ident typ
  | Definition Ident expr
 deriving (Eq, Show, Ord)

data ModuleF unit num typ expr = Module Ident [(Pn,DeclF unit num typ expr)]
 deriving (Eq, Show, Ord)

type PreDecl   = DeclF PreExpr PreExpr PreExpr PreExpr
type Decl a    = DeclF Unit Number Type (Expr a)

type PreModule = ModuleF PreExpr PreExpr PreExpr PreExpr
type Module a  = ModuleF Unit Number Type (Expr a)

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
    PExprParens _ x -> preexprToNumF identF unitF subF inF x
    PExprNeg pn x -> fmap (inF pn . NumNegate) $ subF x
    _ -> parseFail (loc e) $ unwords ["not a valid numeric value",show e]

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

parseTypeOp :: PMonad m => Pn -> Token -> Pn -> Type -> Type -> m Type
parseTypeOp _ SM_ARROW pn t1 t2 = return $ Type pn $ TyArrow t1 t2
parseTypeOp pn tok _ _ _ = parseFail pn $ unwords ["not a valid type operator", show tok]

preexprToType :: PMonad m => PreExpr -> m Type
preexprToType e =
  case e of
    PExprParens _ x -> preexprToType x
    PExprBase (L pn NAT)  -> return (Type pn TyNat)
    PExprBase (L pn INT)  -> return (Type pn TyInt)
    PExprBase (L pn REAL) -> return (Type pn $ TyReal UOne)
    PExprUnit (PExprBase (L pn REAL)) u ->
         do u' <- preexprToUnit u
            return $ Type pn $ TyReal u'
    PExprBinOp t1 (L pn op) t2 ->
         do t1' <- preexprToType t1
            t2' <- preexprToType t2
            parseTypeOp pn op (loc t1) t1' t2'
    PExprQuantify (L pn BIG_LAMBDA) [] e -> preexprToType e
    PExprQuantify (L pn BIG_LAMBDA) (Binder is (Just (PExprUnitKind _)):bs) e -> 
         do e' <- preexprToType (PExprQuantify (L pn BIG_LAMBDA) bs e)
            let f i x = Type (loc i) $ TyUForall i x
            return $ foldr f e' is
    _ -> parseFail (loc e) $ unwords ["not a valid type expression:", show e]

parseExprOp :: PMonad m => Located Token -> Expr () -> Expr () -> m (Expr ())
parseExprOp (L pn tok) x y =
  case tok of
    STAR   -> return $ Expr pn () $ ExprNumber $ NumMult x y
    CDOT   -> return $ Expr pn () $ ExprNumber $ NumMult x y
    SLASH  -> return $ Expr pn () $ ExprNumber $ NumDiv x y
    PLUS   -> return $ Expr pn () $ ExprNumber $ NumPlus x y
    MINUS  -> return $ Expr pn () $ ExprNumber $ NumMinus x y
    HYPHEN -> return $ Expr pn () $ ExprNumber $ NumMinus x y
    TOPOWER -> return $ Expr pn () $ ExprToPower x y
    _ -> parseFail pn $ unwords ["unknown expression operator", show tok]


preexprToExpr :: PMonad m => PreExpr -> m (Expr ())
preexprToExpr e =
  case e of
    PExprParens _ x -> preexprToExpr x
    PExprDecLit pn lit -> fmap (Expr pn () . ExprNumber . NumDec lit) $ interpFloatLit pn lit
    PExprHexLit pn lit -> fmap (Expr pn () . ExprNumber . NumHex lit) $ interpHexLit pn lit
    PExprSuperscript e (L pn exp) ->
         do e' <- preexprToExpr e
            exp' <- parseExp pn exp
            return (Expr (loc e) () $ ExprNumber $ NumToPower e' (fromIntegral exp'))
    PExprBinOp e1 op e2 ->
       do e1' <- preexprToExpr e1
          e2' <- preexprToExpr e2
          parseExprOp op e1' e2'
    PExprIdent i -> return (Expr (loc i) () $ ExprIdent i)
    PExprUnit n u -> 
       do n' <- preexprToNumLit n
          u' <- preexprToUnit u
          return (Expr (loc n) () $ ExprNumLit n' u')
    PExprNeg pn x -> fmap (Expr pn () . ExprNumber . NumNegate) $ preexprToExpr x
    PExprApply x y ->
       do x' <- preexprToExpr x
          y' <- preexprToExpr y
          return (Expr (loc x) () $ ExprApp x' y')
    PExprBase tok -> parseFail (loc tok) $ "invalid expression syntax"
    PExprQuantify tok bs e -> preexprToExpr e >>= unwindExprBinders tok bs
    PExprUnitKind pn -> parseFail pn "'unit' is not a valid expression"

unwindExprBinders :: PMonad m => Located Token -> [Binder] -> Expr () -> m (Expr ())
unwindExprBinders (L pn tok) bs0 e0 =
  case tok of
    SM_LAMBDA -> unwind bs0 
    BIG_LAMBDA -> unwind_big bs0
    _ -> parseFail pn $ unwords ["binder not allowed in expressions:", show tok]
 
 where unwind_big [] = return e0
       unwind_big (Binder is (Just (PExprUnitKind _)) : bs) =
          do e <- unwind_big bs
             return $ unwind_big_is is e
       unwind_big _ = parseFail pn $ "ill formed big lambda"

       unwind_big_is [] e = e
       unwind_big_is (i:is) e = Expr (loc i) () $ ExprUAbs i $ unwind_big_is is e


       unwind [] = return e0
       unwind (Binder is mt : bs) =
            do e <- unwind bs
               mt' <- maybe (return Nothing) (fmap Just . preexprToType) mt
               return $ unwind_is is mt' e

       unwind_is [] _ e = e
       unwind_is (i:is) mt e = Expr (loc i) () $ ExprAbs i mt (unwind_is is mt e)

predeclToDecl :: PMonad m => PreDecl -> m (Decl ())
predeclToDecl d =
  case d of
    QuantityDecl i -> return $ QuantityDecl i
    UnitDecl i is -> return $ UnitDecl i is
    UnitDefn is u -> fmap (UnitDefn is) $ preexprToUnit u
    ConversionDecl n1 n2 -> pure ConversionDecl <*> preexprToNumber n1 <*> preexprToNumber n2
    ConstantDefn is n -> fmap (ConstantDefn is) $ preexprToNumber n
    SymbConstantDefn is e -> fmap (SymbConstantDefn is) $ preexprToExpr e
    PrimDecl id ty -> fmap (PrimDecl id) (preexprToType ty)
    TypeSig id ty -> fmap (TypeSig id) (preexprToType ty)
    Definition id ex -> fmap (Definition id) $ preexprToExpr ex
    

premoduleToModule :: PMonad m => PreModule -> m (Module ())
premoduleToModule (Module i ds) = fmap (Module i) (mapM f ds)
  where f (n,d) = predeclToDecl d >>= \d' -> return (n,d')
