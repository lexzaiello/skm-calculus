module Skm.Eval where

import Skm.Ast
import Skm.Std

eval :: Expr -> Expr
eval (Call (Call K x) _y)         = eval x
eval (Call (Call (Call S x) y) z) =
  let
    x' = eval x
    y' = eval y
    z' = eval z
  in eval (Call (Call x' z') (Call y' z'))
eval (Call M K) = t_k
eval (Call M S) = t_s
eval (Call M M) = t_m
eval (Call M (Call lhs rhs)) =
  let
    lhs' = eval lhs
    rhs' = eval rhs
  in eval (Call t_out (Call (Call M lhs') rhs'))
eval (Call lhs rhs) =
  let
    lhs' = eval lhs
    rhs' = eval rhs
  in
    if (Call lhs' rhs') == (Call lhs rhs) then
      (Call lhs rhs)
    else
      eval (Call lhs' rhs')
eval x = x
