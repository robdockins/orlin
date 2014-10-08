{- Copyright (c) 2014. Robert Dockins. -}

-- | This module defines the 'Comp' compiler monad and associated
--   services, such as error message handling and fresh name generation.
--
module Orlin.Compile where

import System.IO

import Control.Applicative
import qualified Data.Map as M
import Data.Map ( Map )
import Data.List (sortBy, intersperse)

import Orlin.Tokens
import Orlin.AST

-- | Warning and error messages.
data WarnErr
  = Warn (Maybe Pn) String
  | Err  (Maybe Pn) String
 deriving (Eq, Show)

warnErrPn :: WarnErr -> Maybe Pn
warnErrPn (Warn pn _) = pn
warnErrPn (Err pn _) = pn

warnErrComparePn :: WarnErr -> WarnErr -> Ordering
warnErrComparePn x y = compare (warnErrPn x) (warnErrPn y)


-- | State record tracked by the 'Comp' monad
data CompSt
  = CompSt
  { comp_messages   :: [WarnErr]          -- ^ Accumulated error and warning messages
  , comp_expect     :: [(Pn,WarnErr)]     -- ^ The /expected/ error and warning messages, as recorded 
                                          --   in \"pragma expect\" declarations
  , comp_regression :: Bool               -- ^ Are we in static compiler regression mode?
  , comp_debug      :: Bool               -- ^ Are we in compiler debugging mode?
  , comp_fresh      :: !Int               -- ^ Counter for fresh name generation
  }


initialCompSt :: CompSt
initialCompSt = CompSt [] [] False False 0

-- | Main compiler monad.  'Comp' provides a place to stash information
--   accumulated during the compile and tracks error messages, etc.
newtype Comp a = Comp { unComp :: CompSt -> (CompSt, Maybe a) }

instance Monad Comp where
  return x = Comp (\st -> (st, Just x))
  m >>= f  = Comp (\st -> let (st',x) = unComp m st
                           in case x of
                                Nothing -> (st', Nothing)
                                Just y  -> unComp (f y) st')
  fail str = Comp (\st ->
       (st{ comp_messages = comp_messages st ++ [Err Nothing str]}, Nothing))

instance Functor Comp where
  fmap f m = m >>= return . f

instance Applicative Comp where
  pure = return 
  f <*> x = f >>= \f' -> x >>= \x' -> return (f' x')

-- | A failure-recovery combinator.
onFail
   :: a      -- ^ A constant value to return if the main computation fails
   -> Comp a -- ^ A computation to run
   -> Comp a
onFail x m = Comp (\st ->
   case unComp m st of
     (st',Nothing) -> (st', Just x)
     (st',Just y)  -> (st', Just y))

tryComp :: Comp a -> Comp (Maybe a)
tryComp m = Comp $ \st ->
   let (st',x) = unComp m st
    in (st',Just x)

compGetState :: Comp CompSt
compGetState = Comp $ \st -> (st, Just st)

compSetState :: CompSt -> Comp ()
compSetState st = Comp $ \_ -> (st, Just ())

compUpdateState :: (CompSt -> CompSt) -> Comp ()
compUpdateState f = Comp $ \st -> (f st, Just ())


-- | Look up an identifier in the symbol table.  Fail with an error
--   message if the identifier is not in the table.
-- lookupTermIdent :: Ident -> Comp (Symbol SymbolInfo)
-- lookupTermIdent i = do
--    st <- compGetState
--    case st_lookup i (comp_st st) of
--       Nothing -> errMsg (loc i) $ unwords [qt i, "not in scope"]
--       Just info -> return info

-- | Print the given warning and error messages on stderr in order by their position.
displayErrors :: [WarnErr] -> IO ()
displayErrors msgs = mapM_ displayWarnErr (sortBy warnErrComparePn msgs)

-- | Print the given warning/error message on stderr.
displayWarnErr :: WarnErr -> IO ()
displayWarnErr (Warn Nothing msg)   = hPutStrLn stderr $ "warning: "++msg
displayWarnErr (Warn (Just pn) msg) = hPutStrLn stderr $ displayPn pn ++"warning: "++msg
displayWarnErr (Err Nothing msg)    = hPutStrLn stderr $ "error: "++msg
displayWarnErr (Err (Just pn) msg)  = hPutStrLn stderr $ displayPn pn ++ "error: "++msg

-- | Choose a fresh identifier number.
compFreshVar :: Comp Int
compFreshVar = Comp (\compst ->
   let n = comp_fresh compst in
     (compst{ comp_fresh = n+1 }, Just n))

-- | If any error messages have been produced, fail immediately.
phaseFail :: Comp ()
phaseFail = Comp (\compst ->
  if hasErr (comp_messages compst)
        then (compst, Nothing)
        else (compst, Just ()))

-- | Set the compiler into regression test mode
setRegressionMode :: Comp ()
setRegressionMode = Comp (\st -> (st{ comp_regression = True }, Just ()))

-- | Set the compiler into debug mode
setDebugMode :: Comp ()
setDebugMode = Comp (\st -> (st{ comp_debug = True }, Just ()))

-- | Get the debug mode flag
debugMode :: Comp Bool
debugMode = Comp (\st -> (st, Just (comp_debug st)))

-- | Perform an action only when debug mode is enabled
whenDebug :: Comp () -> Comp ()
whenDebug m = debugMode >>= \x -> if x then m else return ()

-- | Record the fact that we expect a warning/error message
addExpect :: Pn -> WarnErr -> Comp ()
addExpect pn x = Comp (\st -> (st{ comp_expect = comp_expect st ++ [(pn,x)] }, Just ()))

-- | Check a list of messages for any errors
hasErr :: [WarnErr] -> Bool
hasErr [] = False
hasErr (Err _ _ : _ ) = True
hasErr (Warn _ _ : xs) = hasErr xs

-- | Record a list of error messages without failing.
addErrs :: [WarnErr] -> Comp ()
addErrs errs = Comp (\st -> (st{ comp_messages = comp_messages st ++ errs }, Just ()))

-- | Record a warning message without failing.
warnMsg :: Pn -> String -> Comp ()
warnMsg pn msg = addErrs [Warn (Just pn) msg]

-- | Record an error message and fail.
errMsg :: Pn -> String -> Comp a
errMsg pn msg = Comp (\st ->
   (st{ comp_messages = comp_messages st ++ [Err (Just pn) msg]
      }, Nothing))

-- -- | Preprocess pragmas before entering the main compiler pipeline.
-- processPragmas :: [(Pn, CodeOrigin, Decl Pn)] -> Comp ()
-- processPragmas prog = mapM_ f prog
--   where f (pn, _, DPragma p) = processPragma pn p
--         f _ = return ()

-- -- | Preprocess a single pragma
-- processPragma :: Pn -> Pragma Pn -> Comp ()
-- processPragma pn (GenericPragma (Ident _ n) tm) = processGPragma pn n tm
-- processPragma pn _ = return ()

-- -- | Preprocess a single generic pragma
-- processGPragma :: Pn -> String -> Maybe PreTerm -> Comp ()
-- processGPragma pn "expect" (Just (PTApplied _ (Ident _ "pconflict") _)) = setRegressionMode
-- processGPragma pn "expect" (Just t) = setRegressionMode >> processExpect t
-- processGPragma pn "expect" Nothing  = errMsg pn "invalid expect pragma"
-- processGPragma pn "debug"  _        = setDebugMode
-- processGPragma _ _ _ = return ()

-- -- | Decompose the preterm of an expect pragma
-- processExpect :: PreTerm -> Comp ()
-- processExpect (PTApplied pn@(Pn f _ _) (Ident _ "error") (PositionalArgs [(_,ln),(_,col)])) = do
--    l <- pretermToNumber ln
--    c <- pretermToNumber col
--    addExpect pn (Err (Just (Pn f l c)) "")

-- processExpect (PTApplied pn@(Pn f _ _) (Ident _ "error") (PositionalArgs [(_,ln),(_,col),(_,msg)])) = do
--    l <- pretermToNumber ln
--    c <- pretermToNumber col
--    m <- pretermToString msg
--    addExpect pn (Err (Just (Pn f l c)) m)

-- processExpect (PTApplied pn@(Pn f _ _) (Ident _ "warning") (PositionalArgs [(_,ln),(_,col)])) = do
--    l <- pretermToNumber ln
--    c <- pretermToNumber col
--    addExpect pn (Warn (Just (Pn f l c)) "")

-- processExpect (PTApplied pn@(Pn f _ _) (Ident _ "warning") (PositionalArgs [(_,ln),(_,col),(_,msg)])) = do
--    l <- pretermToNumber ln
--    c <- pretermToNumber col
--    m <- pretermToString msg
--    addExpect pn (Warn (Just (Pn f l c)) m)


-- processExpect x = errMsg (loc x) "invalid expect pragma"


-- pretermToNumber :: PreTerm -> Comp Int
-- pretermToNumber (PTNumLit _ x) = return (read x)
-- pretermToNumber x = errMsg (loc x) "invalid expect pragma"

-- pretermToString :: PreTerm -> Comp String
-- pretermToString (PTStringLit _ x) = return x
-- pretermToString x = errMsg (loc x) "invalid expect pragma"


-- -- | Check to see if the warning/error messages actually produced
-- --   by the compiler match the ones we expected to get.  Produce
-- --   a new list of error messages indicating any discrepencies.
-- checkExpects :: CompSt -> [WarnErr]
-- checkExpects compst =
--    checkExpects'
--         (sortBy (\x y -> warnErrComparePn (snd x) (snd y)) (comp_expect compst))
--         (sortBy warnErrComparePn (comp_messages compst))

-- checkExpects' :: [(Pn,WarnErr)] -> [WarnErr] -> [WarnErr]
-- checkExpects' (e:es) (m:ms) =
--     if checkExpect e m
--        then checkExpects' es ms
--        else m : checkExpects' (e:es) ms

-- checkExpects' (e:es) [] = map reprocessExpect (e:es)
-- checkExpects' [] (m:ms) = m:ms
-- checkExpects' [] [] = []

-- checkExpect :: (Pn,WarnErr) -> WarnErr -> Bool
-- checkExpect (_, Warn pn1 msg1) (Warn pn2 msg2) = pn1 == pn2 && (null msg1 || msg1 == msg2)
-- checkExpect (_, Err pn1 msg1)  (Err pn2 msg2)  = pn1 == pn2 && (null msg1 || msg1 == msg2)
-- checkExpect _ _ = False

-- reprocessExpect :: (Pn,WarnErr) -> WarnErr
-- reprocessExpect (pn,_) = Err (Just pn) "unsatisfied expect pragma"


-- displayType :: IType -> Comp String
-- displayType (IType t) =
--   case t of
--     TypeName ident [] ->
--        do return $ getIdent ident

--     TypeName ident tys ->
--        do tys' <- mapM displayType tys
--           return $ getIdent ident ++ "(" ++ (concat $ intersperse ", " tys')  ++ ")"

--     TypeList t ->
--        do t' <- displayType t
--           return $ "list("++t'++")"

--     TypeSet t ->
--        do t' <- displayType t
--           return $ "set("++t'++")"

--     TypeMap t1 t2 ->
--        do t1' <- displayType t1
--           t2' <- displayType t2
--           return $ "map("++t1'++", "++t2'++")"

--     TypeTuple tys ->
--        do tys' <- mapM displayType tys
--           return $ concat $ intersperse " * " $ tys'

--     TypeNumber -> return "number"
--     TypeString -> return "string"

--     TypeVar v ->
--         do (pn,x) <- lookupTypeVar v
--            case x of
--              UnboundTyVar -> return $ "#?"++show v
--              RigidTyVar v -> return v
--              BoundTyVar t -> displayType t
