module Orlin.Units where

import           Control.Monad

import           Data.Maybe
import           Data.List
import           Data.Map.Strict( Map )
import qualified Data.Map.Strict as Map
import           Data.Set( Set )
import qualified Data.Set as Set

import Orlin.Tokens(Pn)
import qualified Orlin.AST as AST
import           Orlin.AST (Ident(..), getIdent, loc)
import Orlin.Compile

newtype UVar = UVar Int
 deriving (Eq, Ord, Show)

type USubst = Map UVar (Either String Unit)

-- | A unit is either the very special Zero unit (which characterizes only the 0 constant),
--   or is a map from constant and variable names to occurences.  A negative occurence
--   signifies the inverse unit.  Units are multiplied by adding corresponding occurence numbers,
--   and the inverse of a unit is achieved by negating occurence numbers.
--   The Zero unit annihalates with multiplication, and it is an error to divide by the zero unit.
--   A Left is a reference to a top-level defined constant, and a Right is a local unit variable.
--   Any missing entry in a unit map is understood to be 0.  Furthermore, we maintain the
--   invariant that any existing entry in a unit map is nonzero.
data Unit
  = UnitZero
  | Unit (Map (Either String UVar) Int)
 deriving (Eq,Show,Ord)

displayUnit :: USubst -> Unit -> String
displayUnit usub UnitZero = "0"
displayUnit usub (Unit m)
  | Map.null m = "1"
  | otherwise  =
      concat $ intersperse "·" $ map (uncurry (displayOneUnit usub)) $ Map.toList m

displayOneUnit :: USubst -> Either String UVar -> Int -> String
displayOneUnit usub nm n = either id displayVar nm ++ displayPower n
  where displayVar v =
            case Map.lookup v usub of
              Nothing -> "_u" ++ show v
              Just (Left nm) -> nm
              Just (Right u) -> "(" ++ displayUnit usub u ++ ")"

        displayPower n
          | n == 0 = error "reduced unit raised to 0!"
          | n == 1 = ""
          | otherwise = map toSuper (show n)

        toSuper '1' = '¹'
        toSuper '2' = '²'
        toSuper '3' = '³'
        toSuper '4' = '⁴'
        toSuper '5' = '⁵'
        toSuper '6' = '⁶'
        toSuper '7' = '⁷'
        toSuper '8' = '⁸'
        toSuper '9' = '⁹'
        toSuper '0' = '⁰'
        toSuper '-' = '⁻'
        toSuper '+' = '⁺'
        toSuper c = c


unifyUnitList :: [Unit] -> USubst -> Comp (Maybe ([Unit], USubst))
unifyUnitList []  subst = return  (Just ([],subst))
unifyUnitList [u] subst = return (Just ([u],subst))
unifyUnitList (u1:u2:us) subst =
  do x <- unifyUnits u1 u2 subst
     case x of
        Nothing -> return Nothing
        Just (u1',u2',subst') ->
           do y <- unifyUnitList (u2':us) subst'
              case y of
                 Nothing -> return Nothing
                 Just (us',subst'') ->
                    do let us'' = map (\u -> simplifyUnit u subst'') (u1':us')
                       return (Just (us'', subst''))


unifyUnits :: Unit -> Unit -> USubst -> Comp (Maybe (Unit, Unit, USubst))
unifyUnits UnitZero u subst = return $ Just (UnitZero,u,subst)
unifyUnits u UnitZero subst = return $ Just (u,UnitZero,subst)
unifyUnits u1 u2@(Unit u2map) subst =
   do let u = unitMul u1 (Unit $ fmap negate u2map)
      subst' <- dimUnify u subst
      return $ fmap (\s -> (simplifyUnit u1 s, simplifyUnit u2 s, s)) subst'

simplifyUnit :: Unit -> USubst -> Unit
simplifyUnit UnitZero subst = UnitZero
simplifyUnit (Unit u) subst =
   Map.foldr unitMul unitDimensionless
    $ Map.mapWithKey (\k n ->
            case k of
               Left _ -> Unit $ Map.singleton k n
               Right v ->
                  case Map.lookup v subst of
                    Nothing -> Unit $ Map.singleton k n
                    Just (Left nm) -> Unit $ Map.singleton k n
                    Just (Right x) -> unitToPower' (simplifyUnit x subst) n
               ) u

dimUnify :: Unit -> USubst -> Comp (Maybe USubst)
dimUnify UnitZero subst = return (Just subst)
dimUnify (Unit u) subst =
  case getSmallestVar u subst of
     Nothing -> if Map.null u then return $ Just subst else return Nothing
     Just (final,v,n,u') ->
         if final
            then do
               let uv  = mkUnit $ fmap (\n' -> - (n' `div` n)) u'
               let u'' = mkUnit $ fmap (\n' -> n' `mod` n) u'
               let subst' = Map.insert v (Right uv) subst
               if isDimensionless u'' then return $ Just subst' else return Nothing
            else do
               newvar <- compFreshVar
               let uv  = mkUnit $ Map.insert (Right $ UVar newvar) 1 $ fmap (\n' -> -(n' `div` n)) u'
               let u'' = mkUnit $ Map.insert (Right $ UVar newvar) n $ fmap (\n' -> n' `mod` n) u'
               let subst' = Map.insert v (Right uv) subst
               dimUnify u'' subst'


mkUnit :: Map (Either String UVar) Int -> Unit
mkUnit = Unit . Map.filter (/=0)

isDimensionless :: Unit -> Bool
isDimensionless UnitZero = False
isDimensionless (Unit u) = Map.null u

getSmallestVar
    :: Map (Either String UVar) Int
    -> USubst
    -> Maybe (Bool,UVar,Int,Map (Either String UVar) Int)
getSmallestVar m subst =
  fmap (\(f,v,n) -> (f,v,n,Map.delete (Right v) m)) $ findSmallest m

 where findSmallest :: Map (Either String UVar) Int -> Maybe (Bool,UVar,Int)
       findSmallest = Map.foldrWithKey f Nothing

       f (Left k) n x = x
       f (Right v) n x =
          if isJust $ Map.lookup v subst
             then x
             else case x of
                   Nothing -> Just (True,v,n)
                   Just (_,v',n')
                     | abs n < abs n' -> Just (False,v,n)
                     | otherwise      -> Just (False,v',n')


unitDimensionless :: Unit
unitDimensionless = Unit $ Map.empty

unitConstant :: String -> Unit
unitConstant uname = Unit $ Map.insert (Left uname) 1 Map.empty

unitVar :: UVar -> Unit
unitVar var = Unit $ Map.insert (Right var) 1 Map.empty

unitMul :: Unit -> Unit -> Unit
unitMul UnitZero _ = UnitZero
unitMul _ UnitZero = UnitZero
unitMul (Unit m1) (Unit m2) = Unit $ merge m1 m2
  where merge m1 m2 = Map.mergeWithKey
                        (\_ x y -> let z = x+y in if z == 0 then Nothing else Just z)
                        id id m1 m2

unitToPower' :: Unit -> Int -> Unit
unitToPower' UnitZero n
    | n > 0  = UnitZero
    | n < 0  = error "Orlin.Units.unitToPower': cannot raise zero unit to negative power"
    | n == 0 = Unit Map.empty
    | otherwise = error "Orlin.Units.unitToPower': impossible"
unitToPower' (Unit m) 0 = Unit Map.empty
unitToPower' (Unit m) n = Unit $ fmap (*n) m

unitToPower :: Pn -> Unit -> Int -> Comp Unit
unitToPower pn UnitZero n
    | n > 0  = return $ UnitZero
    | n < 0  = errMsg pn $ "cannot raise zero unit to negative power"
    | n == 0 = return $ Unit Map.empty
    | otherwise = fail "Orlin.Units.unitToPower: impossible"
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
    , unit_ast        :: AST.Unit Ident  -- ^ The syntax of the unit as defined
    , unit_reduced    :: Unit      -- ^ The reduced form of the unit
    }
  | VarUnitInfo
    { unit_canon_name :: String
    , unit_var        :: UVar
    }

 deriving (Eq, Ord, Show)

type QuantitySet = Set String
type UnitTable = Map String UnitInfo


buildUnitEnv :: AST.Module Ident -> Comp (QuantitySet, UnitTable)
buildUnitEnv (AST.Module _ ds) =
   do qty_set <- buildQuantitySet ds
      utbl <- buildUnitTable qty_set ds
      return (qty_set, utbl)

computeReducedUnit :: Pn -> UnitTable -> AST.Unit Ident -> Comp Unit
computeReducedUnit pn utbl u =
  case u of
     AST.UZero    -> return $ UnitZero
     AST.UOne     -> return $ Unit Map.empty
     AST.UIdent i ->
         case Map.lookup (getIdent i) utbl of
            Just BaseUnitInfo{ unit_canon_name = uname } -> return $ unitConstant uname
            Just DerivedUnitInfo{ unit_reduced = red }   -> return $ red
            Just VarUnitInfo{ unit_var = v } -> return $ unitVar v
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
            unitToPower pn u' (fromIntegral exp)


buildQuantitySet :: [(Pn,AST.Decl Ident)] -> Comp QuantitySet
buildQuantitySet = foldM buildQuantitySetDecl Set.empty

buildQuantitySetDecl :: QuantitySet -> (Pn,AST.Decl Ident) -> Comp QuantitySet
buildQuantitySetDecl qty_set (pn,AST.QuantityDecl q) =
    do when (Set.member (getIdent q) qty_set) (errMsg pn $ unwords ["physical quantity already declared:",getIdent q])
       return (Set.insert (getIdent q) qty_set)

buildQuantitySetDecl qty_set _ = return qty_set


buildUnitTable :: Set String -> [(Pn,AST.Decl Ident)] -> Comp UnitTable
buildUnitTable qty_set = foldM (flip $ buildUnitTableDecl qty_set) Map.empty

buildUnitTableDecl :: Set String -> (Pn,AST.Decl Ident) -> UnitTable -> Comp UnitTable
buildUnitTableDecl qty_set (pn,AST.UnitDecl [] qty_name) tb = errMsg pn "internal error: empty unit declaration"
buildUnitTableDecl qty_set (pn,AST.UnitDecl nms@(cname:_) qty_name) tb = foldM (addUnitDecl qty_name cname) tb nms
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
  addUnitDefn :: Ident -> Unit -> AST.Unit Ident -> UnitTable -> Ident -> Comp UnitTable
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