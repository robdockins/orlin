module Orlin.Types where

import           Control.Applicative
import           Data.Ratio
import           Data.Map.Strict( Map )
import qualified Data.Map.Strict as Map

import           Control.Monad.Trans.State
import           Control.Monad.Trans.Class

import qualified Orlin.AST as AST
import           Orlin.AST( Loc(..), Ident(..), getIdent, Binder(..), TypeF(..), ExprF(..), Expr(..), NumF(..) )
import           Orlin.Compile
import           Orlin.Units

type TC a = StateT TCState Comp a

data GType
  = GType (TypeF Unit GType)
  | GTypeVar Int
 deriving (Eq, Show, Ord)
 
initTCState = TCState Map.empty

data TCState
  = TCState
    { tc_tymap :: Map Int GType
    }

runTC :: TC a -> Comp (a, TCState)
runTC m = runStateT m initTCState

type TVar = Int
type TSubst = Map TVar GType


displayType
   :: USubst
   -> TSubst
   -> GType 
   -> String
displayType usub tsub (GTypeVar v) =
  case Map.lookup v tsub of
     Nothing -> "_t" ++ show v
     Just ty -> displayType usub tsub ty
displayType usub tsub (GType x) =
  case x of
    TyInt -> "ℤ"
    TyNat -> "ℕ"
    TyIdent i -> getIdent i
    TyReal (UnitZero) -> "ℝ⟨0⟩"
    TyReal u@(Unit m)
       | Map.null m -> "ℝ"
       | otherwise -> "ℝ〈" ++ displayUnit usub (simplifyUnit u usub) ++ "〉"
    TyArrow t1 t2 -> "("++displayType usub tsub t1 ++ " → " ++ displayType usub tsub t2++")"
    TyUForall i t -> "∀"++(getIdent i)++", "++displayType usub tsub t


type TypeTable = Map String GType

inferType 
   :: UnitTable
   -> TypeTable
   -> Expr ()
   -> USubst
   -> TSubst
   -> Comp (Expr GType, USubst, TSubst)
inferType utab ttab ex@(Expr pn _ x) usub tsub =
  case x of

    ExprNumber _    -> reduceNumber ex >>= \ex' -> inferNumber utab ttab ex' usub tsub

    ExprNumLit nl u ->
      do u' <- computeReducedUnit pn utab u
         let r = reduceNumLit nl
         return (Expr pn (GType (TyReal u')) $ ExprNumber $ NumDec "" r, usub, tsub)

    ExprToPower e n ->
      do (e',usub1,tsub1) <- inferType utab ttab e usub tsub
         uv <- compFreshVar 
         let ty = GType (TyReal (unitVar uv))
         r <- unifyTypes ty (exprTy e') usub1 tsub1
         case r of
           Just (GType (TyReal u'),_,usub2,tsub2) -> do
             u'' <- unitToPower pn u' n
             return (Expr pn (GType (TyReal u'')) $ ExprToPower e' n, usub2, tsub2)
           _ -> errMsg pn $ "expected real number type"

    ExprIdent i -> 
        case Map.lookup (getIdent i) ttab of
          Nothing -> errMsg pn $ unwords ["identifier not in scope:",getIdent i]
          Just ty -> return (Expr pn ty $ ExprIdent i, usub, tsub)

    ExprApp e1 e2 ->
       do (e1',usub1,tsub1) <- inferType utab ttab e1 usub tsub
          (e2',usub2,tsub2) <- inferType utab ttab e2 usub1 tsub1
          resvar <- compFreshVar
          let ty = (GType (TyArrow (exprTy e2') (GTypeVar resvar)))
          r <- unifyTypes ty (exprTy e1') usub2 tsub2
          case r of
             Nothing -> errMsg pn $ unwords ["could not unify"
                                            , displayType usub2 tsub2 (exprTy e1')
                                            , "with"
                                            , displayType usub2 tsub2 ty]
             Just (_,_,usub3,tsub3) ->
                return (Expr pn (GTypeVar resvar) $ ExprApp e1' e2', usub3, tsub3)

    ExprUAbs i e -> do
       uv <- compFreshVar
       let utab' = Map.insert (getIdent i) (VarUnitInfo (getIdent i) uv) utab
       let usub' = Map.insert uv (Left (getIdent i)) usub
       (e', usub'', tsub') <- inferType utab' ttab e usub' tsub
       return (Expr pn (GType (TyUForall i (exprTy e'))) $ ExprUAbs i e', usub'', tsub')

    ExprAbs i mty e -> do
       targ <- case mty of
                  Just ty -> computeReducedType utab ty
                  Nothing -> fmap GTypeVar $ compFreshVar
       let ttab' = Map.insert (getIdent i) targ ttab
       (e',usub',tsub') <- inferType utab ttab' e usub tsub
       return (Expr pn (GType (TyArrow targ (exprTy e'))) $ ExprAbs i mty e', usub', tsub')
       

exprTy :: Expr a -> a
exprTy (Expr _ t _) = t

reduceNumLit :: AST.NumLit -> Rational
reduceNumLit (AST.NumLit pn x) =
  case x of
    NumZero -> 0
    NumDec _ r -> r
    NumHex _ n -> (n%1)
    NumMult x y -> reduceNumLit x * reduceNumLit y
    NumDiv  x y -> reduceNumLit x / reduceNumLit y
    NumPlus x y -> reduceNumLit x + reduceNumLit y
    NumMinus x y -> reduceNumLit x - reduceNumLit y
    NumNegate x -> - reduceNumLit x
    NumToPower x n -> (reduceNumLit x)^n


reduceNumber :: Expr () -> Comp (Expr ())
reduceNumber ex = return ex -- FIXME, implement number folding...

inferNumber 
   :: UnitTable
   -> TypeTable
   -> Expr ()
   -> USubst
   -> TSubst
   -> Comp (Expr GType, USubst, TSubst)
inferNumber utab ttab (Expr pn _ (ExprNumber num)) usub tsub =
   case num of

     NumZero ->
       let ty = GType $ TyReal UnitZero
        in return (Expr pn ty (ExprNumber NumZero), usub, tsub)

     NumDec str r ->
       let ty = GType $ TyReal unitDimensionless
        in return (Expr pn ty (ExprNumber $ NumDec str r), usub, tsub)

     NumHex str r ->
       let ty = GType $ TyReal unitDimensionless
        in return (Expr pn ty (ExprNumber $ NumHex str r), usub, tsub)

     NumMult x y -> do
       (x', usub1,tsub1) <- inferType utab ttab x usub  tsub
       (y', usub2,tsub2) <- inferType utab ttab y usub1 tsub1
       ux <- compFreshVar
       uy <- compFreshVar
       rx <- unifyTypes (GType (TyReal (unitVar ux))) (exprTy x') usub2 tsub2
       case rx of
         Just (GType (TyReal ux'),_,usub3,tsub3) -> do
           ry <- unifyTypes (GType (TyReal (unitVar uy))) (exprTy y') usub3 tsub3
           case ry of
             Just (GType (TyReal uy'),_,usub4,tsub4) -> do
               return (Expr pn (GType (TyReal (unitMul ux' uy'))) $ ExprNumber $ NumMult x' y', usub4, tsub4)
             _ -> errMsg pn $ "real number type expected"
         _ -> errMsg pn $ "real number type expected"

     NumDiv x y -> do
       (x', usub1,tsub1) <- inferType utab ttab x usub  tsub
       (y', usub2,tsub2) <- inferType utab ttab y usub1 tsub1
       ux <- compFreshVar
       uy <- compFreshVar
       rx <- unifyTypes (GType (TyReal (unitVar ux))) (exprTy x') usub2 tsub2
       case rx of
         Just (GType (TyReal ux'),_,usub3,tsub3) -> do
           ry <- unifyTypes (GType (TyReal (unitVar uy))) (exprTy y') usub3 tsub3
           case ry of
             Just (GType (TyReal uy'),_,usub4,tsub4) -> do
               uy'' <- unitInv (loc y) uy'
               return (Expr pn (GType (TyReal (unitMul ux' uy''))) $ ExprNumber $ NumDiv x' y', usub4, tsub4)
             _ -> errMsg pn $ "real number type expected"
         _ -> errMsg pn $ "real number type expected"

     NumToPower x n -> do
       (x', usub1,tsub1) <- inferType utab ttab x usub  tsub
       uv <- compFreshVar 
       let rty = GType (TyReal (unitVar uv))
       r <- unifyTypes rty (exprTy x') usub1 tsub1
       case r of
         Just (GType (TyReal u),_,usub2,tsub2) -> do
           u' <- unitToPower (loc x) u n
           return (Expr pn (GType (TyReal u')) $ ExprNumber $ NumToPower x' n, usub2, tsub2)

         _ -> errMsg pn "real number type required"


     NumNegate x -> do
       (x', usub1,tsub1) <- inferType utab ttab x usub  tsub
       uv <- compFreshVar 
       let rty = GType (TyReal (unitVar uv))
       r <- unifyTypes rty (exprTy x') usub1 tsub1
       case r of
         Nothing -> errMsg pn "real number type required"
         Just (t',_,usub2,tsub2) ->
            return (Expr pn t' $ ExprNumber $ NumNegate x', usub2, tsub2)

     NumPlus x y -> do
       (x', usub1,tsub1) <- inferType utab ttab x usub  tsub
       (y', usub2,tsub2) <- inferType utab ttab y usub1 tsub1
       uv <- compFreshVar 
       let rty = GType (TyReal (unitVar uv))
       r <- unifyTypeList [rty,exprTy x',exprTy y'] usub2 tsub2
       case r of
          Just (rty':_,usub3,tsub3) ->
             return (Expr pn rty' (ExprNumber (NumPlus x' y')), usub3, tsub3)
          _ -> errMsg pn $ unwords [ "could not unify real number types"
                                   , displayType usub2 tsub2 (exprTy x')
                                   , displayType usub2 tsub2 (exprTy y')
                                   ]


     NumMinus x y -> do
       (x', usub1,tsub1) <- inferType utab ttab x usub  tsub
       (y', usub2,tsub2) <- inferType utab ttab y usub1 tsub1
       uv <- compFreshVar 
       let rty = GType (TyReal (unitVar uv))
       r <- unifyTypeList [rty,exprTy x',exprTy y'] usub2 tsub2
       case r of
          Just (rty':_,usub3,tsub3) ->
             return (Expr pn rty' (ExprNumber (NumMinus x' y')), usub3, tsub3)
          _ -> errMsg pn $ unwords [ "could not unify real number types"
                                   , displayType usub2 tsub2 (exprTy x')
                                   , displayType usub2 tsub2 (exprTy y')
                                   ]




inferNumber _ _ (Expr pn _ _) _ _ = errMsg pn "Orlin.Types.inferNumber: impossible!"

computeReducedType :: UnitTable -> AST.Type -> Comp GType
computeReducedType utbl (AST.Type pn ty) =
  case ty of
    TyInt -> return $ GType TyInt
    TyNat -> return $ GType TyNat
    TyReal u -> 
       do u' <- computeReducedUnit pn utbl u
          return $ GType $ TyReal u'
    TyIdent i -> return $ GType $ TyIdent i
    TyArrow t1 t2 ->
          pure (\x y -> GType $ TyArrow x y)
             <*> computeReducedType utbl t1
             <*> computeReducedType utbl t2
    TyUForall i t ->
          fmap (GType . TyUForall i) $ computeReducedType utbl t

unifyTypeList :: [GType] -> USubst -> TSubst -> Comp (Maybe ([GType], USubst, TSubst))
unifyTypeList []  usub tsub = return  (Just ([],usub,tsub))
unifyTypeList [t] usub tsub = return (Just ([t],usub,tsub))
unifyTypeList (t1:t2:ts) usub tsub =
  do x <- unifyTypes t1 t2 usub tsub
     case x of
        Nothing -> return Nothing
        Just (t1',t2',usub',tsub') ->
           do y <- unifyTypeList (t2':ts) usub' tsub'
              case y of
                 Nothing -> return Nothing
                 Just (ts',usub'',tsub'') -> return (Just (t1':ts',usub'',tsub''))

unifyVar :: TVar -> GType -> USubst -> TSubst -> Comp (Maybe (GType, GType, USubst, TSubst))
unifyVar v ty usub tsub =
  case Map.lookup v tsub of
     Nothing ->
        -- FIXME: need to perform occurs check here...
        let tsub' = Map.insert v ty tsub
         in return $ Just (ty,ty,usub,tsub')
     Just ty' -> unifyTypes ty' ty usub tsub


unifyTypes :: GType -> GType -> USubst -> TSubst -> Comp (Maybe (GType, GType, USubst, TSubst))
unifyTypes (GTypeVar v) t2 usub tsub = unifyVar v t2 usub tsub
unifyTypes t1 (GTypeVar v) usub tsub = fmap (fmap (\(t2',t1',usub',tsub') -> (t1',t2',usub',tsub'))) 
                                         $ unifyVar v t1 usub tsub 
unifyTypes t1@(GType TyInt) t2@(GType TyInt) usub tsub =
   return $ Just (t1,t2,usub,tsub)
unifyTypes t1@(GType TyNat) t2@(GType TyNat) usub tsub =
   return $ Just (t1,t2,usub,tsub)
unifyTypes t1@(GType (TyReal u1)) t2@(GType (TyReal u2)) usub tsub =
   do x <- unifyUnits u1 u2 usub
      case x of
        Nothing -> return Nothing
        Just (u1',u2',usub') -> 
          return $ Just (GType (TyReal u1'), GType (TyReal u2'), usub', tsub)
unifyTypes t1@(GType (TyIdent i1)) t2@(GType (TyIdent i2)) usub tsub =
   if getIdent i1 == getIdent i2
      then return $ Just (t1,t2,usub,tsub)
      else return Nothing
unifyTypes (GType (TyArrow s1 s2)) (GType (TyArrow t1 t2)) usub tsub =
   do x <- unifyTypes s1 t1 usub tsub
      case x of
         Nothing -> return Nothing
         Just (s1',t1',usub',tsub') ->
           do y <- unifyTypes s2 t2 usub' tsub'
              case y of
                 Nothing -> return Nothing
                 Just (s2',t2',usub'',tsub'') ->
                    return $ Just (GType (TyArrow s1' s2'), GType (TyArrow t1' t2'), usub'', tsub'')

unifyTypes _ _ _ _ = return Nothing


{-
typeCheckNum :: Pn -> NumF (Expr ()) -> Type -> TC (Expr GType)
typeCheckNum pn num (Type ty_pn (TyReal u)) =
   case num of
      NumZero      -> return (Expr pn (GType (TyReal u)) NumZero)
      NumDec str r
          | u == UZero && r == 0 -> return (Expr pn (GType (TyReal u)) NumZero)
          | u == UZero && r <> 0 -> lift $ errMsg pn $ "non-zero constants cannot be assigned unit 0"
          | otherwise = return (Expr pn (GType (TyReal u) (NumDec str r)))
      NumHex str r
          | u == UZero && r == 0 -> return (Expr pn (GType (TyReal u)) NumZero)
          | u == UZero && r <> 0 -> lift $ errMsg pn $ "non-zero constants cannot be assigned unit 0"
          | otherwise = return (Expr pn (GType (TyReal u) (NumHex str r)))
      NumMult


typeCheckNum pn num _ = lift $ errMsg pn $ "numeric expression must have type 'real'"

typeCheck :: Expr () -> Type -> TC (Expr GType)
typeCheck (Expr pn e) ty =
  case e of
    ExprNumber num -> typeCheckNum pn num ty
    ExprToPower 
-}