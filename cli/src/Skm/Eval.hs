module Skm.Eval where

import Skm.Ast (SkExpr(..))
import Data.Maybe (fromMaybe)

data ReductionMode = Lazy
  | Strict
  deriving (Eq)

newtype EvalConfig = EvalConfig { mode :: ReductionMode }

step :: EvalConfig -> SkExpr -> Maybe SkExpr
step _ (Call (Call K x) _y)             = Just x
step _ (Call (Call (Call S x) y) z)     = Just (Call (Call x z) (Call y z))
step _ _ = Nothing

-- Attempts to reduce the next available outermost redex
evalN :: EvalConfig -> Int -> SkExpr -> SkExpr
evalN cfg n e
  | n <= 0 = e
  | otherwise =
    case e of
      (Call lhs rhs) ->
        let e'  = Call (evalN cfg (n - 1) lhs) rhs
            e'' = fromMaybe e' (step cfg e')
        in
          if e'' == e then
            e
          else
            evalN cfg (n - 2) e''
      x -> x

eval :: EvalConfig -> SkExpr -> SkExpr
eval cfg e =
  case e of
    (Call lhs rhs) ->
      let e'  = Call (eval cfg lhs) rhs
          e'' = fromMaybe e' (step cfg e')
      in
        if e'' == e then
          e
        else
          eval cfg e''
    x -> x
