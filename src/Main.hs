import System.Environment(getArgs)
import Orlin.CmdLine(cmdLine)

main :: IO ()
main = getArgs >>= cmdLine
