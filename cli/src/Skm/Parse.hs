module Skm.Parse where

import Data.Maybe
import Skm.Ast
import Data.String

data Token = LParen
  | RParen
  | St
  | Kt
  | Mt

lex :: String -> [Token]
lex e :: xs =
  (case e of
    "(" -> [LParen]
    ")" -> [RParen]
    "S" -> [St]
    "K" -> [Kt]
    "M" -> [Mt]
    " " -> []) ++ lex xs
lex otherwise = []

parse :: [Token] -> Either (Expr, [Token]) [Token]
parse e :: xs =
  case e of
    St -> Left (S, xs)
    Kt -> Left (K, xs)
    Mt -> Left (M, xs)
    LParen ->
      let (lhs, rest)  <- parse xs
      let (rhs, rest') <- parse rest

      Left (Call lhs rhs, dropparen rest')
    RParen ->
     Right xs
  where dropparen RParen :: xs = xs
        dropparen x            = x
