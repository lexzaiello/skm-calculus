module Main where

import System.IO (hPutStrLn, stderr, putStrLn)
import System.Environment (getArgs)
import Text.Read (readMaybe)
import Data.List (elem)
import Skm.Ast
import Skm.Parse
import Skm.Eval

bold :: String -> String
bold s = "\ESC[1m" ++ s ++ "\ESC[0m"

-- In order of precedence. Earlier commands short-circuit
cmds =

isflag :: String -> Bool
isflag s = take 2 s == "--"

-- Only flags, but with -- removed
flags :: [String] -> [String]
flags = (map (drop 2)) . (filter isflag)

cmds :: [String] -> [String]
cmds = filter $ not isflag

-- Selects lam calc preprocessor if enabled
parser :: [String] -> (String -> Either String Expr)
parser args =
  if "lc" `elem` (flags args) then
    todo
  else
    

execcmd :: [String] -> IO (Either String ())
execcmd args =
  

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("help":_) ->
      putStrLn $ (bold "skm eval <EXPR>")     ++ " - evaluates an SKM expression. Does not typecheck the expression. Not guaranteed to terminate.\n"
                 ++ (bold "skm check <EXPR>") ++ " - typechecks the expression.\n"
                 ++ (bold "skm help")         ++ " - prints this help message.\n"
                 ++ (bold "skm --lc <CMD> <EXPR>") ++ " - runs the lambda calculus preprocessor first.\n"
    args ->
      
    _ -> pure ()
