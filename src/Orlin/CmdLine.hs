module Orlin.CmdLine where

import Control.Applicative
import           Data.Map.Strict( Map )
import qualified Data.Map.Strict as Map
import           Data.Set( Set )
import qualified Data.Set as Set

import System.IO
import System.Exit

import Orlin.Tokens( Pn(..), displayPn )
import Orlin.Parser
import Orlin.Lexer
import Orlin.AST
import Orlin.Units
import Orlin.Compile

import System.Console.Shell
import System.Console.Shell.ShellMonad
import System.Console.Shell.Backend.Haskeline

data REPL = 
  REPL
  { qty_set :: QuantitySet
  , unit_table :: UnitTable
  , comp_state :: CompSt
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
  , helpCommand "help"
  ]

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
evalCmd (UnifyUnits is us) =
  do shellPutStrLn $ unwords $ ["attempting to unify"]++map show us
     st <- getShellSt
     (vs,subst) <- runShComp $ do
         vs <- mapM (const compFreshVar) is
         let utb = foldr (\(i,v) -> Map.insert (getIdent i) (VarUnitInfo (getIdent i) v))
                         (unit_table st) 
                         (zip is vs)
         us' <- mapM (computeReducedUnit (Pn "" 0 0) utb) us
         x <- unifyUnitList us' Map.empty
         return (vs,x)
     case subst of
       Nothing -> shellPutStrLn "units do not unify"
       Just (us_final,s) -> do
           mapM_ (shellPutStrLn . show) us_final
           shellPutStrLn "unifier"
           let showUnifier (i,v) = do
                 let u = fmap (\u -> simplifyUnit u s) $ Map.lookup v s
                 shellPutStrLn $ unwords [getIdent i,"("++show v++")","=",show u]
           mapM_ showUnifier $ zip is vs
           shellPutStrLn "subst table"
           mapM_ (shellPutStrLn . show) $ Map.toList s

cmdLine :: [String] -> IO ()
cmdLine [x] = 
 do (q,ut,st) <- buildUnitEnv' x
    runrepl (REPL q ut st)
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

buildUnitEnv' :: String -> IO (QuantitySet, UnitTable, CompSt)
buildUnitEnv' fp = do
  mod <- openFile fp ReadMode >>= hGetContents >>=
             either printErrs return . runModuleParser fp >>= premoduleToModule
  let (st', x) = unComp (buildUnitEnv mod) initialCompSt
  displayErrors (comp_messages st')
  case x of
     Nothing -> exitFailure
     Just (q,ut) -> return (q,ut,st')

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

displayModule :: Module () -> IO ()
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
