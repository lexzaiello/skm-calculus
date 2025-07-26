module Skm.Parse where

import Data.Maybe
import Skm.Ast
import Data.String

data Token = LParen
  | RParen
  | St
  | Kt
  | Mt

-- Outputs the offending token if a token was inputted incorrectly
lexi :: String -> Either String [Token]
lexi (e:xs) = do
  let tok <- (case e of
    '('       -> pure LParen
    ')'       -> pure RParen
    'S'       -> pure St
    'K'       -> pure Kt
    'M'       -> pure Mt
    otherwise -> Left $ "unexpected token: " ++ otherwise)
  pure $ tok ++ (<- lexi xs)
lexi otherwise = pure []

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
