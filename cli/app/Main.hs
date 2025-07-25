module Main where

import System.IO (hPutStrLn, stderr, putStrLn)
import Skm.Ast
import Skm.Parse
import Skm.Eval

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["eval", expr] ->
      case (parse . lex) expr of
        Left (e, _) ->
          putStrLn $ (show . eval) e
        Right _ ->
          hPutStrLn stderr "parsing failed"
