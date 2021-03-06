module Orlin.CmdLine where

import           Control.Applicative

import           Data.Map.Strict( Map )
import qualified Data.Map.Strict as Map
import           Data.Set( Set )
import qualified Data.Set as Set
-- import           Data.Graph

import System.IO
import System.Exit



import Orlin.Tokens( Pn(..), displayPn )
import Orlin.Parser
import Orlin.Lexer
import Orlin.AST as AST
import Orlin.Units
import Orlin.Compile
import qualified Orlin.PureTypeSys as PTS
-- import Orlin.Types
-- import Orlin.ModuleTC

import System.Console.Shell
import System.Console.Shell.ShellMonad
import System.Console.Shell.Backend.Haskeline


data REPL = 
  REPL
  { qty_set :: QuantitySet
  , unit_table :: UnitTable
  , comp_state :: CompSt
  , repl_module :: AST.Module Ident
  }

runrepl :: REPL -> IO REPL
runrepl init =
  let desc = (mkShellDescription commands evaluate)
             { greetingText = Just "Welcome to Orlin!\n"
             , historyFile = Just "orlin.history"
             }
   in runShell desc haskelineBackend init

commands :: [ShellCommand REPL]
commands =
  [ exitCommand "quit"
  , exitCommand "q"
  , helpCommand "help"
--  , cmd "reorder" reorderCmd  "reorder module declarations" 
  ]

{-
reorderCmd :: Sh REPL ()
reorderCmd = 
  do mod <- fmap repl_module $ getShellSt
     (i,ds) <- runShComp $ reorderModule mod
     shellPutStrLn $ unlines $ map showSCC $ ds

showSCC :: Show a => SCC a -> String
showSCC (AcyclicSCC x) = show x
showSCC (CyclicSCC xs) = 
  unlines $ [ "cycle" ] ++ [ "  " ++ show x | x <- xs ]
-}

instance Applicative (Sh a) where
  pure = return
  f <*> x = f >>= \f' -> x >>= \x' -> return $ f' x'

instance PMonad (Sh a) where
  parseFail pn msg = fail $ unwords [displayPn pn, msg]

evaluate :: String -> Sh REPL ()
evaluate str =
  case runCommandParser str of
     Left errs -> mapM_ (\(pn,m) -> shellPutErrLn $ unwords [displayPn pn,m]) errs
     Right precmd -> preREPL2REPL precmd >>= evalCmd

runShComp :: Comp a -> Sh REPL a
runShComp m = do
   st <- getShellSt
   let (comp_st', x) = unComp m (comp_state st)
   mapM_ shellDisplayMsg (comp_messages comp_st')
   putShellSt st{ comp_state = comp_st'{ comp_messages = [] } }
   maybe (fail "command failed") return x

shellDisplayMsg (Warn Nothing msg)   = shellPutErrLn msg
shellDisplayMsg (Warn (Just pn) msg) = shellPutErrLn $ unwords [displayPn pn, msg]
shellDisplayMsg (Err Nothing msg)    = shellPutErrLn msg
shellDisplayMsg (Err (Just pn) msg)  = shellPutErrLn $ unwords [displayPn pn, msg]

evalCmd :: REPLCommand -> Sh REPL ()
evalCmd DoNothing = return ()

evalCmd (Typecheck e) =
     do (sm,vm,tym,cs,expr,typ) <- runShComp $ PTS.checkOneExpr e
        shellPutStrLn expr
        shellPutStrLn typ
        mapM_ ( shellPutStrLn . show) $ Set.toList cs

-- evalCmd (Typecheck e) =
--   do -- shellPutStrLn $ unwords $ ["attempting to typecheck",show e]
--      shellPutStrLn ""
--      st <- getShellSt
--      (t,usub,tsub) <- runShComp $ inferType (unit_table st) Map.empty e Map.empty Map.empty
--      shellPutStrLn $ displayType usub tsub (exprTy t)

-- evalCmd (UnifyTypes is ts) =
--   do -- shellPutStrLn $ unwords $ ["attempting to unify"]++map show ts
--      st <- getShellSt
--      (vs,x) <- runShComp $ do
--          vs <- mapM (const compFreshVar) is
--          let utb = foldr (\(i,v) -> Map.insert (getIdent i) (VarUnitInfo (getIdent i) v))
--                          (unit_table st) 
--                          (zip is vs)
--          ts' <- mapM (computeReducedType utb) ts
--          x <- unifyTypeList ts' Map.empty Map.empty
--          return (vs,x)
--      case x of
--         Nothing -> shellPutStrLn "types do not unify"
--         Just (ts_final,usub,tsub) -> do
--            mapM_ (shellPutStrLn . displayType usub tsub) ts_final
--            shellPutStrLn "unifier:"
--            let showUnifier (i,v) = do
--                  let u = fmap (either unitConstant (\u -> simplifyUnit u usub)) $ Map.lookup v usub
--                  let showu = maybe ("_u"++show v) (displayUnit usub) u
--                  shellPutStrLn $ unwords [" ",getIdent i,"=",showu]
--            mapM_ showUnifier $ zip is vs
--            shellPutStrLn "subst table"
--            mapM_ (shellPutStrLn . show) $ Map.toList usub

evalCmd (UnifyUnits is us) =
  do -- shellPutStrLn $ unwords $ ["attempting to unify"]++map show us
     st <- getShellSt
     (vs,subst) <- runShComp $ do
         vs <- mapM (const (UVar <$> compFreshVar)) is
         let utb = foldr (\(i,v) -> Map.insert (getIdent i) (VarUnitInfo (getIdent i) v))
                         (unit_table st) 
                         (zip is vs)
         us' <- mapM (computeReducedUnit (Pn "" 0 0) utb) us
         x <- unifyUnitList us' Map.empty
         return (vs,x)
     case subst of
       Nothing -> shellPutStrLn "units do not unify"
       Just (us_final,usub) -> do
           --mapM_ (shellPutStrLn . displayUnit) us_final
           shellPutStrLn $ displayUnit usub $ head us_final 
           shellPutStrLn "unifier:"
           let showUnifier (i,v) = do
                 let u = fmap (either unitConstant (\u -> simplifyUnit u usub)) $ Map.lookup v usub
                 let showu = maybe ("_u"++show v) (displayUnit usub) u
                 shellPutStrLn $ unwords [" ",getIdent i,"=",showu]
           mapM_ showUnifier $ zip is vs

cmdLine :: [String] -> IO ()
cmdLine [x] =
 do (q,ut,st,mod) <- buildUnitEnv' x
    runrepl (REPL q ut st mod)
    return ()

--cmdLine = mapM_ buildAndPrintUnitEnv
--cmdLine = mapM_ parseAndPrint'

printUnitEnv :: (QuantitySet, UnitTable) -> IO ()
printUnitEnv (qty_set,utbl) =
  do putStrLn "Quantities" 
     mapM_ print $ Set.toList qty_set
     putStrLn ""
     putStrLn "Units"
     mapM_ print $ Map.toList utbl

buildUnitEnv' :: String -> IO (QuantitySet, UnitTable, CompSt, AST.Module AST.Ident)
buildUnitEnv' fp = do
  mod <- openFile fp ReadMode >>= hGetContents >>=
             either printErrs return . runModuleParser fp >>= premoduleToModule
  let (st', x) = unComp (buildUnitEnv mod) initialCompSt
  displayErrors (comp_messages st')
  case x of
     Nothing -> exitFailure
     Just (q,ut) -> return (q,ut,st',mod)

buildAndPrintUnitEnv :: String -> IO ()
buildAndPrintUnitEnv fp = do
  mod <- openFile fp ReadMode >>= hGetContents >>=
             either printErrs return . runModuleParser fp >>= premoduleToModule
  let (st', x) = unComp (buildUnitEnv mod) initialCompSt
  displayErrors (comp_messages st')
  case x of
     Nothing -> return ()
     Just env -> printUnitEnv env

instance PMonad IO where
  parseFail pn msg = fail $ unwords [displayPn pn, msg]

printErrs :: [(Pn,String)] -> IO a
printErrs = fail . unlines . map (\(pn,msg) -> unwords [displayPn pn, msg])

displayModule :: Module Ident -> IO ()
displayModule (Module ident ds) =
   do putStrLn $ unwords ["module",show ident]
      mapM_ (print . snd) ds

parseAndPrint' :: String -> IO ()
parseAndPrint' fp =
  openFile fp ReadMode >>= hGetContents >>= either printErrs return . runModuleParser fp >>= premoduleToModule >>= displayModule

parseAndPrint :: String -> IO ()
parseAndPrint fp = 
  openFile fp ReadMode >>= hGetContents >>= print . runModuleParser fp

parseAndLex :: String -> IO ()
parseAndLex fp =
  openFile fp ReadMode >>= hGetContents >>=
     putStrLn . unlines . map show . runlexer
