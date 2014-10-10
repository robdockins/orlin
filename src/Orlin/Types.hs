module Orlin.Types where

import           Data.Map.Strict( Map )
import qualified Data.Map.Strict as Map

import           Control.Monad.Trans.State
import           Control.Monad.Trans.Class

import qualified Orlin.AST as AST
import           Orlin.AST( Loc(..), Ident(..), getIdent, Binder(..), TypeF(..), ExprF(..), Expr(..), NumF(..) )
import           Orlin.Compile

type TC a = StateT TCState Comp a

data GType
  = GType (TypeF GType)
  | GTypeVar Int
 deriving (Eq, Show, Ord)
 
initTCState = TCState Map.empty

data TCState
  = TCState
    { tc_tymap :: Map Int GType
    }

runTC :: TC a -> Comp (a, TCState)
runTC m = runStateT m initTCState

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