module Orlin.CmdLine where

import System.IO

import Orlin.Tokens( Pn, displayPn )
import Orlin.Parser
import Orlin.Lexer
import Orlin.AST

cmdLine :: [String] -> IO ()
cmdLine = mapM_ parseAndPrint'

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
