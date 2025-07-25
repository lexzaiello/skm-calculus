module Main where

import System.IO (hPutStrLn, stderr, putStrLn)
import System.Environment (getArgs)
import Skm.Ast
import Skm.Parse
import Skm.Eval

bold :: String -> String
bold s = "\ESC[1m" ++ s ++ "\ESC[0m"

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("help":_) ->
      putStrLn $ (bold "skm eval <EXPR>")     ++ " - evaluates an SKM expression. Does not typecheck the expression. Not guaranteed to terminate.\n"
                 ++ (bold "skm check <EXPR>") ++ " - typechecks the expression.\n"
                 ++ (bold "skm help")         ++ " - prints this help message.\n"
    ["eval", expr] ->
      case (parse . lexi) expr of
        Right (e, _) ->
          putStrLn $ (show . eval) e
        Left _ ->
          hPutStrLn stderr "parsing failed"
    [] -> pure ()
