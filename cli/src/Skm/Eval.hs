module Skm.Eval where

import Control.Applicative
import Skm.Ast
import Data.Maybe (fromMaybe)

data EvalConfig = EvalConfig
  { tIn   :: Expr
  , tOut  :: Expr
  , tK    :: Expr
  , tS    :: Expr
  , tM    :: Expr
  , arrow :: Expr
  }

step :: EvalConfig -> Expr -> Maybe Expr
step _ (Call (Call K x) _y)              = Just x
step _ (Call (Call (Call S x) y) z)      = Just (Call (Call x z) (Call y z))
step (EvalConfig { tK = tK }) (Call M K) = Just tK
step (EvalConfig { tS = tS }) (Call M S) = Just tS
step (EvalConfig { tM = tM }) (Call M M) = Just tM
step (EvalConfig { tOut = tOut })
  (Call M (Call lhs rhs))                = Just (Call (Call (Call M lhs) rhs) tOut)
step _ _ = Nothing

-- Attempts to reduce the next available outermost redex
eval_n :: EvalConfig -> Int -> Expr -> Expr
eval_n cfg n e
  | n <= 0 = e
  | otherwise =
    case e of
      (Call lhs rhs) ->
        let e'  = (Call (eval_n cfg (n - 1) lhs) rhs)
            e'' = fromMaybe e' (step cfg e')
        in
          if e'' == e then
            e
          else
            eval_n cfg (n - 2) e''
      x -> x

eval :: EvalConfig -> Expr -> Expr
eval cfg e =
  case e of
    (Call lhs rhs) ->
      let e'  = (Call (eval cfg lhs) rhs)
          e'' = fromMaybe e' (step cfg e')
      in
        if e'' == e then
          e
        else
          eval cfg e''
    x -> x
