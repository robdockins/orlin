module Orlin.CmdLine where

import           Data.Map.Strict( Map )
import qualified Data.Map.Strict as Map
import           Data.Set( Set )
import qualified Data.Set as Set

import System.IO

import Orlin.Tokens( Pn, displayPn )
import Orlin.Parser
import Orlin.Lexer
import Orlin.AST
import Orlin.Units
import Orlin.Compile

cmdLine :: [String] -> IO ()
cmdLine = mapM_ buildAndPrintUnitEnv
--cmdLine = mapM_ parseAndPrint'

printUnitEnv :: (QuantitySet, UnitTable) -> IO ()
printUnitEnv (qty_set,utbl) =
  do putStrLn "Quantities" 
     mapM_ print $ Set.toList qty_set
     putStrLn ""
     putStrLn "Units"
     mapM_ print $ Map.toList utbl

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

displayModule :: (Show unit, Show number, Show expr) => Module unit number expr -> IO ()
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
