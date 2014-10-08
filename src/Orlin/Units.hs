module Orlin.Units where

import           Control.Monad

import           Data.Map.Strict( Map )
import qualified Data.Map.Strict as Map
import           Data.Set( Set )
import qualified Data.Set as Set

import Orlin.Tokens(Pn)
import qualified Orlin.AST as AST
import           Orlin.AST (Ident(..), getIdent, loc)
import Orlin.Compile

-- | A unit is either the very special Zero unit (which characterizes only the 0 constant),
--   or is a map from constant and variable names to occurences.  A negative occurence
--   signifies the inverse unit.  Units are multiplied by adding corresponding occurence numbers,
--   and the inverse of a unit is achieved by negating occurence numbers.
--   The Zero unit annihalates with multiplication, and it is an error to divide by the zero unit.
--   A Left is a reference to a top-level defined constant, and a Right is a local unit variable.
--   Any missing entry in a unit map is understood to be 0.
data Unit 
  = UnitZero
  | Unit (Map (Either String String) Integer)
 deriving (Eq,Show,Ord)

unitDimensionless :: Unit
unitDimensionless = Unit $ Map.empty

unitConstant :: String -> Unit
unitConstant uname = Unit $ Map.insert (Left uname) 1 Map.empty

unitVar :: String -> Unit
unitVar var = Unit $ Map.insert (Right var) 1 Map.empty

unitMul :: Unit -> Unit -> Unit
unitMul UnitZero _ = UnitZero
unitMul _ UnitZero = UnitZero
unitMul (Unit m1) (Unit m2) = Unit $ merge m1 m2
  where merge m1 m2 = Map.mergeWithKey 
                        (\_ x y -> let z = x+y in if z == 0 then Nothing else Just z)
                        id id m1 m2

unitToPower :: Pn -> Unit -> Integer -> Comp Unit
unitToPower pn UnitZero n
    | n > 0  = return $ UnitZero
    | n < 0  = errMsg pn $ "cannot raise zero unit to negative power"
    | n == 0 = return $ Unit Map.empty
unitToPower _ (Unit m) 0 = return $ Unit Map.empty
unitToPower _ (Unit m) n = return $ Unit $ fmap (*n) m


unitInv :: Pn -> Unit -> Comp Unit
unitInv pn UnitZero = errMsg pn "cannot take the inverse of the zero unit"
unitInv pn (Unit m) = return $ Unit $ fmap negate m

-- | Combine two units additively.  This checks that non-zero units
--   are equal, and if one argument is Zero, the output is the other argument.
--   If two non-zero units are not equal, Nothing is returned.
addUnits :: Unit -> Unit -> Maybe Unit
addUnits UnitZero u = Just u
addUnits u UnitZero = Just u
addUnits u@(Unit u1) (Unit u2) =
    if u1 == u2 then Just u else Nothing

data UnitInfo
  = BaseUnitInfo
    { unit_qty_name   :: String    -- ^ The quantity class of the unit
    , unit_canon_name :: String    -- ^ The canonical name of the unit (used in unit maps)
    }
  | DerivedUnitInfo
    { unit_canon_name :: String
    , unit_ast        :: AST.Unit  -- ^ The syntax of the unit as defined
    , unit_reduced    :: Unit      -- ^ The reduced form of the unit
    }

 deriving (Eq, Ord, Show) 

type QuantitySet = Set String
type UnitTable = Map String UnitInfo


buildUnitEnv :: AST.Module AST.Unit a b -> Comp (QuantitySet, UnitTable)
buildUnitEnv (AST.Module _ ds) =
   do qty_set <- buildQuantitySet ds
      utbl <- buildUnitTable qty_set ds
      return (qty_set, utbl)

computeReducedUnit :: Pn -> UnitTable -> AST.Unit -> Comp Unit
computeReducedUnit pn utbl u =
  case u of
     AST.UZero    -> return $ UnitZero
     AST.UOne     -> return $ Unit Map.empty
     AST.UIdent i ->
         case Map.lookup (getIdent i) utbl of
            Just BaseUnitInfo{ unit_canon_name = uname } -> return $ unitConstant uname
            Just DerivedUnitInfo{ unit_reduced = red }   -> return $ red
            Nothing -> errMsg (loc i) $ unwords ["unit name not in scope:", getIdent i]
     AST.UMult u1 u2 ->
         do u1' <- computeReducedUnit pn utbl u1
            u2' <- computeReducedUnit pn utbl u2
            return $ unitMul u1' u2'
     AST.UDiv u1 u2 ->
         do u1' <- computeReducedUnit pn utbl u1
            u2' <- computeReducedUnit pn utbl u2
            fmap (unitMul u1') (unitInv pn u2')
     AST.UToPower u exp -> 
         do u' <- computeReducedUnit pn utbl u
            unitToPower pn u' exp


buildQuantitySet :: [(Pn,AST.Decl AST.Unit a b)] -> Comp QuantitySet
buildQuantitySet = foldM buildQuantitySetDecl Set.empty

buildQuantitySetDecl :: QuantitySet -> (Pn,AST.Decl AST.Unit a b) -> Comp QuantitySet
buildQuantitySetDecl qty_set (pn,AST.QuantityDecl q) = 
    do when (Set.member (getIdent q) qty_set) (errMsg pn $ unwords ["physical quantity already declared:",getIdent q])
       return (Set.insert (getIdent q) qty_set)

buildQuantitySetDecl qty_set _ = return qty_set


buildUnitTable :: Set String -> [(Pn,AST.Decl AST.Unit a b)] -> Comp UnitTable
buildUnitTable qty_set = foldM (flip $ buildUnitTableDecl qty_set) Map.empty

buildUnitTableDecl :: Set String -> (Pn,AST.Decl AST.Unit a b) -> UnitTable -> Comp UnitTable
buildUnitTableDecl qty_set (pn,AST.UnitDecl qty_name []) tb = errMsg pn "internal error: empty unit declaration"
buildUnitTableDecl qty_set (pn,AST.UnitDecl qty_name nms@(cname:_)) tb = foldM (addUnitDecl qty_name cname) tb nms
  where
    addUnitDecl :: Ident -> Ident -> UnitTable -> Ident -> Comp UnitTable
    addUnitDecl qty_name cname tb uname =
     do unless (Set.member (getIdent qty_name) qty_set)
               (errMsg (loc qty_name) $ unwords ["unknown physical quantity:",getIdent qty_name])
        case Map.lookup (getIdent uname) tb of
          Just _ -> errMsg (loc uname) $ unwords ["unit name already bound in scope:", getIdent uname]
          Nothing -> do let tb' = Map.insert (getIdent uname)
                                           (BaseUnitInfo
                                            { unit_qty_name = getIdent qty_name
                                            , unit_canon_name = getIdent cname
                                            })
                                           tb
                        return tb'

buildUnitTableDecl qty_set (pn,AST.UnitDefn [] _) tb = errMsg pn "internal error: empty unit definition"
buildUnitTableDecl qty_set (pn,AST.UnitDefn nms@(cname:_) u) tb =
  do red <- computeReducedUnit pn tb u
     foldM (addUnitDefn cname red u) tb nms

 where
  addUnitDefn :: Ident -> Unit -> AST.Unit -> UnitTable -> Ident -> Comp UnitTable
  addUnitDefn cname u uast tb uname =
     case Map.lookup (getIdent uname) tb of
        Just _ -> errMsg (loc uname) $ unwords ["unit name already bound in scope:", getIdent uname]
        Nothing -> do let tb' = Map.insert (getIdent uname)
                                         (DerivedUnitInfo
                                         { unit_canon_name = getIdent cname
                                         , unit_ast = uast
                                         , unit_reduced = u
                                         })
                                         tb
                      return tb'

buildUnitTableDecl qty_set _ tb = return tb