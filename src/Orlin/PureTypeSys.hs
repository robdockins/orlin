{-# LANGUAGE DeriveGeneric #-}

module Orlin.PureTypeSys where

import Prelude hiding (mapM)
import Control.Applicative
import Control.Monad.State.Strict hiding (mapM)

import Data.Traversable
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Orlin.Units
import Orlin.Tokens(Pn)
import Orlin.Compile
import qualified Orlin.AST as AST

newtype Index = Idx Int
 deriving( Eq, Ord, Show )

newtype EVar = EVar Int
 deriving( Eq, Ord, Show )

-- FIXME? what should qualified identifiers be?
data QIdent
  = QId String 
 deriving( Eq, Ord, Show )

data Sort
  = SType
  | SUnit
  | SKind
  | SSort
  | SEVar EVar
 deriving ( Eq, Ord, Show )

-- | `ThSubst i vs` defines a substitution on deBruijn variables.
--   The `i` indicates how many binders we have passed under, and the
--   `vs` gives values for the free variables above `i` to be substituted. 

data Thunk
  = ThSubst !Int !(Seq Expr)
  | ThShift !Int !Int
 deriving( Eq, Ord, Show )

data Expr
  = Var Index
  | EEVar (Seq Thunk) EVar
  | Lambda String Expr Sort Expr
  | Pi String Expr Sort Expr
  | App Expr Expr
  | Let LetDecl Expr
  | ExprIdent QIdent Expr
  | ExprNumLit AST.NumLit Unit
  | ExprNum (AST.NumF Expr) Expr
  | Base (AST.BaseType Unit)
  | Sort Sort
 deriving( Eq, Ord, Show )

unfoldSort :: Sort -> TC Sort
unfoldSort s@(SEVar ev) =
   do st <- get
      let sm = sortMap st
      case Map.lookup ev sm of
        Just s' -> unfoldSort s'
        Nothing -> return s
unfoldSort s = return s

unfoldExpr :: Expr -> TC Expr
unfoldExpr x =
  case x of
    EEVar thunks ev ->
       do st <- get
          let vm = exprMap st
          case Map.lookup ev vm of
           Just t -> applyThunks thunks t >>= unfoldExpr
           Nothing -> return x
    Lambda nm ty s body ->
       do ty' <- unfoldExpr ty
          s' <- unfoldSort s
          body' <- unfoldExpr body
          return (Lambda nm ty' s' body')
    Pi nm ty s body ->
       do ty' <- unfoldExpr ty
          s' <- unfoldSort s
          body' <- unfoldExpr body
          return (Pi nm ty' s' body')
    App x y ->
       pure App <*> unfoldExpr x <*> unfoldExpr y

    Let (NonRecDecl nm x ty s) y ->
       do x' <- unfoldExpr x
          ty' <- unfoldExpr ty
          s' <- unfoldSort s
          y' <- unfoldExpr y
          return (Let (NonRecDecl nm x' ty' s') y')

    Sort s -> pure Sort <*> unfoldSort s

    _ -> return x


seq_lookup :: Seq a -> Index -> a
seq_lookup seq (Idx i) = Seq.index seq (Seq.length seq - 1 - i)

displayExpr :: Seq String -> Expr -> TC String
displayExpr nms (Var v) = return $ seq_lookup nms v

displayExpr nms (EEVar thunks ev@(EVar ev')) =
   do st <- get
      let vm = exprMap st
      case Map.lookup ev vm of
        Just t  -> applyThunks thunks t >>= displayExpr nms
        Nothing -> return $ "#"++show ev'

displayExpr nms (Lambda nm ty _ ex) =
   do let nm' = nm -- FIXME disambiguate shadowing
      ty' <- displayExpr nms ty
      ex' <- displayExpr (nms Seq.|> nm') ex
      return $ "(𝛌" ++ nm' ++ ":" ++ ty' ++ ", " ++ ex' ++ ")"

displayExpr nms (Pi nm ty _ ex) =
   do let nm' = nm -- FIXME disambiguate shadowing
      ty' <- displayExpr nms ty
      ex' <- displayExpr (nms Seq.|> nm') ex
      return $ "(∀" ++ nm' ++ ":" ++ ty' ++ ", " ++ ex' ++ ")"

displayExpr nms (Let (NonRecDecl nm x ty _) y) =
   do let nm' = nm -- FIXME disambiguate shadowing
      ty' <- displayExpr nms ty
      x' <- displayExpr nms x
      y' <- displayExpr (nms Seq.|> nm') y
      return $ "(let " ++ nm' ++ ":" ++ ty' ++ " = " ++ x' ++ "; in " ++ y' ++")"

displayExpr nms (App x y) =
    do x' <- displayExpr nms x
       y' <- displayExpr nms y
       return $ unwords [x',y']

displayExpr nms (Let (RecDecl xs) y) =
      error "display reclet!"

displayExpr nms (ExprIdent (QId id) _) =
      return id

displayExpr nms (ExprNumLit nl u) =
      error "display numlits!"

displayExpr nms (ExprNum num ty) =
      error "display nums!"

displayExpr nms (Base bt) = return $ show bt -- FIXME

displayExpr nms (Sort (SEVar sv@(EVar sv'))) =
    do st <- get
       let sm = sortMap st
       case Map.lookup sv sm of
         Just s -> displayExpr nms (Sort s)
         Nothing -> return $ "#"++show sv'

displayExpr nms (Sort s) = return $ show s  -- FIXME



incThunk :: Int -> Thunk -> Thunk
incThunk n (ThSubst i vs) = ThSubst (i+n) vs
incThunk n (ThShift i j)  = ThShift (i+n) j

applyThunksVar :: Seq Thunk -> Int -> TC Expr
applyThunksVar thunks v =
  case Seq.viewr thunks of
    thunks' Seq.:> (ThSubst i vs)
       | v >= i && (v-i) >= Seq.length vs -> applyThunksVar thunks' (v - Seq.length vs)
       | v >= i -> applyThunks (thunks' Seq.|> ThShift 0 i) (seq_lookup vs (Idx (v-i)))
       | otherwise -> applyThunksVar thunks' v

    thunks' Seq.:> (ThShift i j)
       | v >= i    -> applyThunksVar thunks' (v+j)
       | otherwise -> applyThunksVar thunks' v

    Seq.EmptyR -> return $ Var (Idx v)


applyThunks :: Seq Thunk -> Expr -> TC Expr
applyThunks thunks ex =
 case ex of
   Var (Idx v) -> applyThunksVar thunks v

   EEVar thunks' ev ->   
     do st <- get
        let vm = exprMap st
        case Map.lookup ev vm of
          Just t  -> applyThunks (thunks Seq.>< thunks') t
          Nothing -> return $ EEVar (thunks Seq.>< thunks') ev

   Lambda nm typ sort x ->
     do let thunks' = fmap (incThunk 1) thunks
        typ' <- applyThunks thunks typ
        x' <- applyThunks thunks' x
        return (Lambda nm typ' sort x')

   Pi nm typ sort x ->
     do let thunks' = fmap (incThunk 1) thunks
        typ' <- applyThunks thunks typ
        x' <- applyThunks thunks' x
        return (Pi nm typ' sort x')

   App x y -> pure App <*> applyThunks thunks x <*> applyThunks thunks y

   Let (NonRecDecl nm x typ s) y ->
     do let thunks' = fmap (incThunk 1) thunks
        x' <- applyThunks thunks x
        typ' <- applyThunks thunks typ
        y' <- applyThunks thunks' y
        return (Let (NonRecDecl nm x' typ' s) y')

   Let (RecDecl xs) y ->
     do xs' <- mapM f xs
        y'  <- applyThunks thunks' y
        return (Let (RecDecl xs') y')

    where thunks' = fmap (incThunk n) thunks
          n = length xs
          f (nm,x,typ,s) = do
             x' <- applyThunks thunks' x
             typ' <- applyThunks thunks typ
             return (nm,x',typ',s)

   ExprIdent ident ty -> ExprIdent ident <$> applyThunks thunks ty
   ExprNum nm ty -> ExprNum <$> traverse (applyThunks thunks) nm <*> applyThunks thunks ty
   ExprNumLit _ _ -> return ex
   Base _ -> return ex
   Sort _ -> return ex


subst :: Seq Expr -> Expr -> TC Expr
subst vs x
  | Seq.length vs == 0 = return x
  | otherwise = applyThunks (Seq.singleton (ThSubst 0 vs)) x

shift :: Int -> Expr -> TC Expr
shift 0 x = return x
shift j x = applyThunks (Seq.singleton (ThShift 0 j)) x



data LetDecl
  = NonRecDecl String Expr Expr Sort
  | RecDecl [(String, Expr, Expr, Sort)]
 deriving( Eq, Ord, Show )

-- type contexts bind the types of local variables
-- together with the sort (of the type)
type Context = Seq (Expr, Sort)

data Symbol
  = SymExpr Expr Expr Sort  -- expr, type, sort
  | SymUnit String Unit     -- canonical name, reduced unit
  | SymQuantity String      -- canonical name
 deriving( Eq, Ord, Show )

-- a scope binds a names to symbols
type Scope = Map String (Pn, Symbol)

-- An environment is a sequence of nested scopes, with innermost
-- scopes at the beginning of the list.  A name is looked up in
-- an environment by examining scopes from innermost to outermost,
-- chosing the first binding that matches.
type Env = Seq Scope

data Constraint
  = CUnify Pn Expr Expr
  | CProdRel Pn Sort Sort Sort
  | CSortRel Pn Sort Sort
  | CCheck Pn Context Expr Expr
  | CNumericType Pn Expr
 deriving( Eq, Ord, Show )

type CSet = Set Constraint

type VarMap = Map EVar Expr
type SortMap = Map EVar Sort

-- a map from names to local variables.
-- NOTE the int here is opposite deBruijn indices: 0 is outermost,
-- not innermost.  To get deBruijn indicies, take (depth - n),
-- where depth is the number of surrounding binders.
type LocalScope = Map String Int


lookup_env :: String -> Env -> Maybe (Pn,Symbol)
lookup_env ident env =
  case Seq.viewl env of
    s Seq.:< env' ->
      case Map.lookup ident s of
        Just x -> Just x
        Nothing -> lookup_env ident env'
    Seq.EmptyL -> Nothing


data TCState =
  TCState
  { sortMap :: SortMap
  , exprMap :: VarMap
  , typeMap :: VarMap
  }

typeOf :: Seq Expr -> Expr -> TC Expr
typeOf ctx (Var i@(Idx n))
  | n < Seq.length ctx = return $ seq_lookup ctx i
  | otherwise = fail $ unwords ["unbound de Brujin index in typeOf",show i, show ctx]
typeOf _ (EEVar thunks ev) =
  do st <- get
     case Map.lookup ev (typeMap st) of
       Just ty -> applyThunks thunks ty
       Nothing -> fail $ unwords ["evar missing type mapping!: ", show ev]
typeOf ctx (Lambda nm ty s body) =
  do body' <- typeOf (ctx Seq.|> ty) body
     return (Pi nm ty s body')
typeOf ctx (Pi nm ty s body) =
  do body' <- typeOf (ctx Seq.|> ty) body
     return body'
typeOf ctx (App f x) =
  do (Pi _ _ _ body) <- typeOf ctx f
     subst (Seq.singleton x) body
typeOf ctx (Let (NonRecDecl _ _ ty _) e) =
  typeOf (ctx Seq.|> ty) e
typeOf ctx (Let (RecDecl ds) e) =
  do let ctx' = Seq.fromList $ map (\(_,_,ty,_) -> ty) ds
     typeOf (ctx Seq.>< ctx') e
typeOf ctx (ExprIdent q ty) =
  return ty
typeOf ctx (ExprNumLit _ u) =
  return $ Base $ AST.BaseReal u
typeOf ctx (ExprNum num ty) =
  return ty
typeOf ctx (Base _) =
  return $ Sort SType
typeOf ctx (Sort _) =
  return $ Sort SSort


type TC a = StateT TCState Comp a

setEVarSort :: EVar -> Sort -> TC ()
setEVarSort ev s = 
   modify (\st -> st{ sortMap = Map.insert ev s (sortMap st) })

setEVarExpr :: EVar -> Expr -> TC ()
setEVarExpr ev ex =
   modify (\st -> st{ exprMap = Map.insert ev ex (exprMap st) })

-- NOTE expr is assumed to be in WHNF
unifyEVar :: Pn -> Env -> Seq Thunk -> EVar -> (Maybe Blocker, Expr) -> TC CSet
unifyEVar pn env thunks ev (blk,x) =
  do st <- get
     let vm = exprMap st
     case Map.lookup ev vm of
        Just t  -> (applyThunks thunks t >>= whnf pn) >>= unify pn env (blk,x)
        Nothing ->
          if Seq.length thunks == 0
             then setEVarExpr ev x >> return Set.empty
             else go x

 where
  go (Var idx) = lift $ errMsg pn $ unwords ["FIXME don't know how to unify evars with vars :("]

  go (EEVar thunks' ev') =
       do st <- get
          let vm = exprMap st
          case Map.lookup ev' vm of
            Just t -> applyThunks thunks' t >>= go
            Nothing -> return $ Set.singleton (CUnify pn (EEVar thunks ev) x)

  go (Lambda nm ty s body) =
     do ty' <- freshExpr thunks (Sort s)
        body' <- freshExpr thunks ty'
        setEVarExpr ev (Lambda nm ty' s body')
        c1 <- simplifyConstraint env (CUnify pn ty ty')
        c2 <- simplifyConstraint env (CUnify pn body body')
        return (Set.unions [c1,c2])

  go (Pi nm ty s body) = 
     do ty' <- freshExpr thunks (Sort s)
        body' <- freshExpr thunks ty'
        setEVarExpr ev (Pi nm ty' s body')
        c1 <- simplifyConstraint env (CUnify pn ty ty')
        c2 <- simplifyConstraint env (CUnify pn body body')
        return (Set.union c1 c2)
   
  go (App x y) =  -- FIXME?? higher-order-unification?
     do tyx <- typeOf Seq.empty x -- FIXME? is empty context correct?
        tyy <- typeOf Seq.empty y

        x' <- freshExpr thunks =<< applyThunks thunks tyx
        y' <- freshExpr thunks =<< applyThunks thunks tyy
        setEVarExpr ev (App x' y')

        c1 <- simplifyConstraint env (CUnify pn x x')
        c2 <- simplifyConstraint env (CUnify pn y y')
        return (Set.unions [c1,c2])
        
  go (Let _ _) = lift $ errMsg pn $ unwords ["internal error: unify expr expected to be in WHNF"]

  go (ExprNum _ _)
     = lift $ errMsg pn $ unwords ["FIXME: don't know how to unify numeric expressions..."]

  go (ExprIdent _ _) =
     do setEVarExpr ev x
        return Set.empty

  go (ExprNumLit _ _) =
     do setEVarExpr ev x
        return Set.empty

  go (Base _) =
     do setEVarExpr ev x
        return Set.empty

  go (Sort _) =
     do setEVarExpr ev x
        return Set.empty



data Blocker
  = BlockEVar EVar 
  | BlockIdent QIdent
  | BlockVar Index
 

whnf :: Pn -> Expr -> TC (Maybe Blocker, Expr)
whnf pn x@(EEVar _ ev)        = return (Just (BlockEVar ev), x)
whnf pn x@(ExprIdent ident _) = return (Just (BlockIdent ident), x)
whnf pn x@(Var idx)           = return (Just (BlockVar idx), x)
whnf pn (App x y) =
   do res <- whnf pn x
      case res of
         (Just blk, x') -> return (Just blk, App x' y)
         (_, Lambda _ _ _ body) -> subst (Seq.singleton y) body >>= whnf pn
         (_,x') -> lift $ errMsg pn $ unwords ["unexpected result of whnf:", show x']

whnf pn (Let (NonRecDecl nm x _ _) body) =
   subst (Seq.singleton x) body >>= whnf pn

whnf pn (Let (RecDecl _) _) = lift $ errMsg pn $ unwords ["don't try to evaluate recursive definitions when typechecking!"]

whnf pn x = return (Nothing, x)

simplifyConstraint :: Env -> Constraint -> TC CSet
simplifyConstraint env (CUnify pn (EEVar thunks ev) y) = whnf pn y >>= unifyEVar pn env thunks ev
simplifyConstraint env (CUnify pn x (EEVar thunks ev)) = whnf pn x >>= unifyEVar pn env thunks ev
simplifyConstraint env (CUnify pn x y) =
  do x' <- whnf pn x
     y' <- whnf pn y
     unify pn env x' y'

simplifyConstraint env (CCheck pn ctx exp ty) = checkExpr pn env ctx exp ty
simplifyConstraint env (CProdRel pn s1 s2 s3) = checkProdRel pn s1 s2 s3
simplifyConstraint env (CSortRel pn s1 s2) = checkSortRel pn env s1 s2

simplifyConstraint _ c = return $ Set.singleton c
     
unifyUnits :: Pn -> Expr -> Expr -> TC CSet
unifyUnits pn x y = undefined

checkProdRel :: Pn -> Sort -> Sort -> Sort -> TC CSet
checkProdRel pn s1 s2 s3 =
    do unifySort pn s2 s3
       join (pure check <*> getSort s1 <*> getSort s2)
 where
   check s1@(SEVar _) s2@(SEVar _) = return $ Set.singleton (CProdRel pn s1 s2 s2)
   check SType s2    = unifySort pn s2 SType
   check SUnit s2    = unifySort pn s2 SType
   check SKind SType = return $ Set.empty
   check SKind SUnit = lift $ errMsg pn $ "units may not depend on types"
   check s1 SKind    = unifySort pn s1 SKind
   check s1 SUnit    = unifySort pn s1 SUnit
   check s1 s2       = return $ Set.singleton (CProdRel pn s1 s2 s2)

checkSortRel :: Pn -> Env -> Sort -> Sort -> TC CSet
checkSortRel pn env s1 s2 = join (pure check <*> getSort s1 <*> getSort s2)
 where
   check s1@(SEVar _) s2@(SEVar _) = return $ Set.singleton (CSortRel pn s1 s2)
   check SType s2 = unifySort pn s2 SKind
   check SUnit s2 = unifySort pn s2 SKind
   check SKind _  = lift $ errMsg pn $ "'kind' cannot be typed"
   check _ SType  = lift $ errMsg pn $ "'type' classifes no sorts"
   check _ SUnit  = lift $ errMsg pn $ "'unit' classifes no sorts"
   check s1 SKind = return $ Set.singleton (CSortRel pn s1 SKind)


getSort :: Sort -> TC Sort
getSort s@(SEVar ev) =
   do st <- get
      case Map.lookup ev (sortMap st) of
        Just s' -> getSort s'
        Nothing -> return s
getSort s = return s
  


checkExpr :: Pn -> Env -> Context -> Expr -> Expr -> TC CSet
checkExpr pn env ctx ex ty =
 do ex' <- whnf pn ex
    case snd ex' of
       EEVar thunks ev ->
         do st <- get
            let vm = exprMap st
            case Map.lookup ev vm of
              Just t  -> applyThunks thunks t >>= \t' -> checkExpr pn env ctx t' ty
              Nothing -> return $ Set.singleton (CCheck pn ctx (snd ex') ty)

       Sort s' ->
            do s <- freshSort
               c1 <- simplifyConstraint env (CSortRel pn s' s)
               c2 <- simplifyConstraint env (CUnify pn ty (Sort s))
               return (Set.unions [c1,c2])

       Base bt -> simplifyConstraint env (CUnify pn ty (Sort SType))

       Var idx -> 
          let (ty',s') = seq_lookup ctx idx
           in simplifyConstraint env (CUnify pn ty ty')

       App x y ->
         do s <- freshSort
            s' <- freshSort
            a <- freshExpr Seq.empty (Sort s)
            b <- freshExpr Seq.empty (Sort s')
            let typx = (Pi "_" a s b)
            c1 <- checkExpr pn env ctx x typx
            c2 <- checkExpr pn env ctx y a
            b' <- subst (Seq.singleton y) b
            c3 <- simplifyConstraint env (CUnify pn ty b')
            return (Set.unions [c1,c2,c3])

       Pi nm a s1 b ->
         do s2 <- freshSort
            s3 <- freshSort
            c1 <- checkExpr pn env ctx a (Sort s1)
            c2 <- checkExpr pn env (ctx Seq.|> (a,s1)) b (Sort s2)
            c3 <- simplifyConstraint env (CProdRel pn s1 s2 s3)
            c4 <- simplifyConstraint env (CUnify pn ty (Sort s3))
            return (Set.unions [c1,c2,c3,c4])

       Lambda nm a s body ->
         do s' <- freshSort
            b <- freshExpr Seq.empty (Sort s')
            c1 <- checkExpr pn env ctx (Pi nm a s b) (Sort s')
            c2 <- checkExpr pn env (ctx Seq.|> (a,s)) body b
            c3 <- simplifyConstraint env (CUnify pn ty (Pi nm a s b))
            return (Set.unions [c1,c2,c3])

       ExprIdent (QId ident) ty2 ->
         case lookup_env ident env of
           Just (_,SymExpr _ ty' s') ->
             do c1 <- simplifyConstraint env (CUnify pn ty ty')
                c2 <- simplifyConstraint env (CUnify pn ty ty2)
                return (Set.unions [c1,c2])
           _ -> lift $ errMsg pn $ unwords [ident,"not in scope"]

       ExprNumLit num u ->
         simplifyConstraint env (CUnify pn ty (Base (AST.BaseReal u)))

      {- ExprNum ... FIXME -}
      {- Let .... FIXME -}


unifySort :: Pn -> Sort -> Sort -> TC CSet
unifySort pn (SEVar sv) s =
  do st <- get
     let sm = sortMap st
     case Map.lookup sv sm of
       Just s' -> unifySort pn s' s
       Nothing -> setEVarSort sv s >> return Set.empty
unifySort pn s (SEVar sv) = unifySort pn (SEVar sv) s
unifySort pn s1 s2
  | s1 == s2 = return Set.empty
  | otherwise = lift $ errMsg pn $ unwords ["cannot unify",show s1,"with",show s2]


-- NOTE, inputs assumed to be in WHNF and not EVars
unify :: Pn -> Env -> (Maybe Blocker, Expr) -> (Maybe Blocker, Expr) -> TC CSet
unify pn _ (_,Var idx1) (_,Var idx2)
  | idx1 == idx2 = return Set.empty
  | otherwise = lift $ errMsg pn $ unwords ["cannot unify variable", show idx1, "with", show idx2]

unify pn env (_,Pi nm1 typ1 sort1 body1) (_,Pi nm2 typ2 sort2 body2) =
  do c1 <- simplifyConstraint env (CUnify pn typ1 typ2)
     c2 <- unifySort pn sort1 sort2
     c3 <- simplifyConstraint env (CUnify pn body1 body2)
     return $ Set.unions [c1,c2,c3]

unify pn env (Just (BlockVar idx1), App x1 y1) (Just (BlockVar idx2), App x2 y2)
  | idx1 == idx2 =
       do c1 <- unify pn env (Just (BlockVar idx1), x1) (Just (BlockVar idx2), x2)
          c2 <- simplifyConstraint env (CUnify pn y1 y2)
          return (Set.unions [c1,c2])
  | otherwise = lift $ errMsg pn $ unwords ["cannot unify variable",show idx1, "with", show idx2]

unify pn env (Just (BlockIdent ident1), App x1 y1) (Just (BlockIdent ident2), App x2 y2)
  | ident1 == ident2 =
       do c1 <- unify pn env (Just (BlockIdent ident1), x1) (Just (BlockIdent ident2), x2)
          c2 <- simplifyConstraint env (CUnify pn y1 y2)
          return (Set.union c1 c2)
  | otherwise = lift $ errMsg pn $ unwords ["cannot unify",show ident1, "with", show ident2]

unify pn _ (Just (BlockEVar _), x) (_,y) =
  return $ Set.singleton (CUnify pn x y)

unify pn _ (_,x) (Just (BlockEVar _), y) =
  return $ Set.singleton (CUnify pn x y)

unify pn _ (_,ExprIdent (QId ident1) _) (_,ExprIdent (QId ident2) _)
  | ident1 == ident2 = return Set.empty
  | otherwise = lift $ errMsg pn $ unwords ["cannot unify",ident1,"with",ident2]

unify pn _ (_,Sort s1) (_,Sort s2) = unifySort pn s1 s2

unify pn _ (_,Base b1) (_,Base b2)
  | b1 == b2 = return Set.empty -- FIXME unify units
  | otherwise = lift $ errMsg pn $ unwords ["cannot unify",show b1,"with", show b2]

unify pn _ (_,x) (_,y) = lift $ errMsg pn $ unwords ["cannot unify", show x, "with", show y]



{-
  | EEVar (Seq Thunk) EVar

data Constraint
  = CUnify Pn Expr Expr
  | CProdRel Pn Sort Sort Sort
  | CCheck Pn Context Expr Sort
  | CNumericType Pn Expr
 deriving( Eq, Ord, Show )
-}

unionCS :: TC CSet -> TC CSet -> TC CSet
unionCS x y = pure Set.union <*> x <*> y

freshExpr :: Seq Thunk -> Expr -> TC Expr
freshExpr thunks ty =
  do v <- lift $ compFreshVar
     modify (\st -> st{ typeMap = Map.insert (EVar v) ty (typeMap st) })
     return $ EEVar thunks $ EVar v

freshSort :: TC Sort
freshSort =
  do v <- lift $ compFreshVar
     return $ SEVar $ EVar v


checkOneExpr :: AST.Expr AST.Ident -> Comp (SortMap, VarMap, VarMap, CSet, String, String)
checkOneExpr expr =
   do ((cs,expr',typ),TCState sm vm tym) <- runStateT dotc (TCState Map.empty Map.empty Map.empty)
      return (sm,vm,tym,cs,expr',typ)
 where dotc =
        do s <- freshSort
           typ <- freshExpr Seq.empty (Sort s)
           let env = Seq.empty
           (cs, expr') <- generateConstraints env Seq.empty Map.empty 0 expr typ
           cs' <- simplifyConstraints env cs

           str_expr <- displayExpr Seq.empty expr' 
           str_typ <- displayExpr Seq.empty typ

           -- str_expr <- show <$> unfoldExpr expr'
           -- str_typ  <- show <$> unfoldExpr typ

           return (cs', str_expr, str_typ)

-- FIXME, this algorithm is really naive!
simplifyConstraints :: Env -> CSet -> TC CSet
simplifyConstraints env = loop
 where
    loop cs =
       do cs' <- simpl cs
          if cs == cs' then return cs else loop cs'
    simpl cs = Set.unions <$> (mapM (simplifyConstraint env) $ Set.toList cs)


generateConstraints
   :: Env             -- identifier environment
   -> Context         -- local variable context
   -> LocalScope      -- binding from identifiers to local variable indicies
   -> Int             -- current binder depth
   -> AST.Expr AST.Ident -- the AST expression to typecheck
   -> Expr            -- the expected type of the expression
   -> TC (CSet, Expr)
generateConstraints env ctx locals depth (AST.Expr pn ex) typ =
 case ex of
   AST.ExprIdent ident
     | Just n <- Map.lookup (AST.getIdent ident) locals ->
        do let i = depth - 1 - n
           case Seq.viewl $ Seq.drop n ctx of
             ((typ',sort') Seq.:< _) ->
               do typ'' <- shift (i+1) typ' -- shift the type into the current context

                  c1 <- simplifyConstraint env (CUnify pn typ typ'')

                  -- FIXME, this check may not be necessary if we maintain the invariant
                  -- that we do this check every time we extend the context...
                  c2 <- simplifyConstraint env (CCheck pn ctx typ'' (Sort sort'))
                  return (Set.unions [c1,c2], Var $ Idx i)

             Seq.EmptyL -> lift $ errMsg pn $ unwords ["internal error: out of bounds local variable", AST.getIdent ident, show ctx, show locals, show depth, show i]

     -- symbol types are supposed to be closed, no shifting needed
     | Just (_,SymExpr _ typ' sort') <- lookup_env (AST.getIdent ident) env ->
               do c1 <- simplifyConstraint env (CUnify pn typ typ')
                  return (c1, ExprIdent (QId $ AST.getIdent ident) typ')

     | otherwise -> lift $ errMsg pn $ unwords ["identifier not in scope or not an expression:", AST.getIdent ident]

   AST.ExprForall ident mt b ->
     do s1 <- freshSort
        s2 <- freshSort
        s3 <- freshSort
        (c0,a') <- case mt of
                    Nothing -> freshExpr Seq.empty (Sort s1) >>= \a -> return (Set.singleton (CCheck pn ctx a (Sort s1)), a)
                    Just a -> generateConstraints env ctx locals depth a (Sort s1)
        (c1,b') <- generateConstraints
                      env 
                      (ctx Seq.|> (a',s1))
                      (Map.insert (AST.getIdent ident) depth locals)
                      (depth+1)
                      b (Sort s2)
        c2 <- simplifyConstraint env (CUnify pn typ (Sort s3))
        c3 <- simplifyConstraint env (CProdRel pn s1 s2 s3)
        return (Set.unions [c0,c1,c2,c3],  Pi (AST.getIdent ident) a' s1 b')

   AST.ExprArrow a b -> 
     do s1 <- freshSort
        s2 <- freshSort
        s3 <- freshSort
        (c0,a') <- generateConstraints env ctx locals depth a (Sort s1)
        (c1,b') <- generateConstraints env ctx locals depth b (Sort s2)
        c2 <- simplifyConstraint env (CUnify pn typ (Sort s3))
        c3 <- simplifyConstraint env (CProdRel pn s1 s2 s3)
        b'' <- shift 1 b'
        return (Set.unions [c0,c1,c2,c3], Pi "_" a' s1 b'')
     
   AST.ExprAbs ident mt x ->
     do s <- freshSort
        s' <- freshSort
        (c0,a) <- case mt of
                    Nothing -> freshExpr Seq.empty (Sort s) >>= \a -> return (Set.singleton (CCheck pn ctx a (Sort s)), a)
                    Just t -> generateConstraints env ctx locals depth t (Sort s)
        b <- freshExpr Seq.empty (Sort s')
        let typ' = Pi (AST.getIdent ident) a s b
        (c1,x') <- generateConstraints
                      env 
                      (ctx Seq.|> (a,s))
                      (Map.insert (AST.getIdent ident) depth locals)
                      (depth+1)
                      x b
        c2 <- simplifyConstraint env (CCheck pn ctx typ' (Sort s'))
        c3 <- simplifyConstraint env (CUnify pn typ typ')
        return (Set.unions [c0, c1, c2, c3], Lambda (AST.getIdent ident) a s x')

   AST.ExprApp x y ->
     do s <- freshSort
        s' <- freshSort
        a <- freshExpr Seq.empty (Sort s)
        b <- freshExpr Seq.empty (Sort s')
        let typx = (Pi "_" a s b)
        (c1,x') <- generateConstraints env ctx locals depth x typx
        (c2,y') <- generateConstraints env ctx locals depth y a
        b' <- subst (Seq.singleton y') b
        c3 <- simplifyConstraint env (CUnify pn typ b')
        return (Set.unions [c1,c2,c3], App x' y')

   AST.ExprNumLit nm u ->
     do u' <- Orlin.PureTypeSys.computeReducedUnit pn env ctx locals depth u
        c1 <- simplifyConstraint env (CUnify pn typ (Base (AST.BaseReal u')))
        return (c1, ExprNumLit nm u')

   AST.ExprNumber num ->
     do (c0,num') <- traverse id <$> traverse (\x -> generateConstraints env ctx locals depth x typ) num
        return (c0, ExprNum num' typ)

   AST.ExprSort s ->
     do c0 <- simplifyConstraint env (CUnify pn typ (Sort SKind))
        let s' = translateSort s
        return (c0, Sort s')

   AST.ExprBase base ->
     do base' <- traverse (Orlin.PureTypeSys.computeReducedUnit pn env ctx locals depth) base
        c0 <- simplifyConstraint env (CUnify pn typ (Sort SType))
        return (c0, Base base')

translateSort :: AST.Sort -> Sort
translateSort AST.SUnit = SUnit
translateSort AST.SType = SType

pairMap :: (a -> b) -> (c -> d) -> (a,c) -> (b,d)
pairMap f g (x,y) = (f x, g y)

computeReducedUnit :: Pn -> Env -> Context -> LocalScope -> Int -> AST.Unit AST.Ident -> TC Unit
computeReducedUnit pn env ctx locals depth u = undefined pn env ctx locals depth u

