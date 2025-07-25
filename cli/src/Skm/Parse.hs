module Skm.Parse where

import Data.Maybe
import Skm.Ast
import Data.String

data Token = LParen
  | RParen
  | St
  | Kt
  | Mt

lexi :: String -> [Token]
lexi (e:xs) =
  (case e of
    '('       -> [LParen]
    ')'       -> [RParen]
    'S'       -> [St]
    'K'       -> [Kt]
    'M'       -> [Mt]
    otherwise -> []) ++ lexi xs
lexi otherwise = []

parse :: [Token] -> Either [Token] (Expr, [Token])
parse (e:xs) =
  case e of
    St -> pure (S, xs)
    Kt -> pure (K, xs)
    Mt -> pure (M, xs)
    LParen -> do
      (lhs, rest)  <- parse xs
      (rhs, rest') <- parse rest

      pure (Call lhs rhs, dropparen rest')
    RParen ->
     Left xs
  where dropparen (RParen:xs) = xs
        dropparen x              = x
