module Orlin.CmdLine where

import System.IO
import Orlin.Parser
import Orlin.Lexer

cmdLine :: [String] -> IO ()
cmdLine = mapM_ parseAndPrint

parseAndPrint :: String -> IO ()
parseAndPrint fp = 
  openFile fp ReadMode >>= hGetContents >>= print . runModuleParser fp

parseAndLex :: String -> IO ()
parseAndLex fp =
  openFile fp ReadMode >>= hGetContents >>=
     putStrLn . unlines . map show . runlexer
