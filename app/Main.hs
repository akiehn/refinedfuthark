module Main where

import RefinedFuthark.Parser (parseFile, Program, ParseError)
import RefinedFuthark.TypeCheck (typeCheck)
import RefinedFuthark.Pretty (prettyFuthark)
import RefinedFuthark.Transform (erase)
import System.Exit (die)
import System.Console.GetOpt
import System.Environment (getArgs)
import RefinedFuthark.Syntax (Dec(ImportDec))

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute optDescrs args of
    --(opts,nonopts,[]) -> mapM_ (\f -> readFile f >>= handle f) nonopts
    ([],[file],[]) -> readFile file >>= handle file >>= putStrLn
    ([outfile],[file],[]) -> readFile file >>= handle file >>= writeFile outfile
    (_,_,errors) -> die (concat errors ++ usageInfo usage optDescrs)
  where optDescrs = [Option ['o'] [] (ReqArg id "FILE") "output FILE"]

usage :: String
usage = "Usage: refinedfuthark [options] FILE"

handle :: String -> String -> IO String
handle file contents = case parseFile file contents of
  --Right (ImportDec dep : p) -> (readFile f >>= handle f)
  Right p -> do
    p' <- handleImports p
    case typeCheck p' of
      Right c -> return (prettyFuthark (erase p))--("Parsed file " ++ f) >> putStrLn (show c)
      Left e -> die (show e)
  Left e -> die (show e)

handleImports :: Program -> IO Program
handleImports (ImportDec dep : p) = do
  contents <- readFile (dep ++ ".rfut")
  p' <- tryParse (dep ++ ".rfut") contents
  decs1 <- handleImports p'
  decs2 <- handleImports p
  return (decs1 ++ decs2)
handleImports decs = return decs

tryParse :: String -> String -> IO Program
tryParse file contents = case parseFile file contents of
  Right p -> return p
  Left e -> die (show e)
