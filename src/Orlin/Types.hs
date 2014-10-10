module Orlin.Types where

import           Control.Applicative
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

computeReducedType :: UnitTable -> AST.Type -> Comp GType
computeReducedType utbl (AST.Type pn ty) =
  case ty of
    TyInt -> return $ GType TyInt
    TyNat -> return $ GType TyNat
    TyReal u -> 
       do u' <- computeReducedUnit pn utbl u
          return $ GType $ TyReal u'
    TyIdent i -> return $ GType $ TyIdent i
    TyArrow t1 t2 -> pure (\x y -> GType $ TyArrow x y) <*> computeReducedType utbl t1 <*> computeReducedType utbl t2


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