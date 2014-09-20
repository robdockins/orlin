module Orlin.CmdLine where

import System.IO
import Orlin.Parser

cmdLine :: [String] -> IO ()
cmdLine = mapM_ parseAndPrint

parseAndPrint :: String -> IO ()
parseAndPrint fp = 
  openFile fp ReadMode >>= hGetContents >>=  print . runModuleParser fp