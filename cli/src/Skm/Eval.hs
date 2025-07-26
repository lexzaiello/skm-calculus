module Skm.Eval where

import Skm.Ast
import Skm.Std
import Data.Maybe (fromMaybe)

step :: Expr -> Maybe Expr
step (Call (Call K x) _y) = Just x
step (Call (Call (Call S x) y) z) = Just (Call (Call x z) (Call y z))
step (Call M K) = Just t_k
step (Call M S) = Just t_s
step (Call M M) = Just t_m
step (Call M (Call lhs rhs)) = Just (Call t_out (Call (Call M lhs) rhs))
step _ = Nothing

-- Attempts to reduce the next available outermost redex
eval_n :: Int -> Expr -> Expr
eval_n 0 e = e
eval_n n e =
  case e of
    (Call lhs rhs) ->
      eval_n (n - 2) (Call (eval_n (n - 1) lhs) (eval_n (n - 1) rhs))
    x -> x

eval :: Expr -> Expr
eval e =
  case e of
    (Call lhs rhs) ->
      let call' = (Call (eval lhs) (eval rhs))
          e'    = fromMaybe call' $ step call' in
        if e' == e then
          e
        else
          eval e'
    x -> x
