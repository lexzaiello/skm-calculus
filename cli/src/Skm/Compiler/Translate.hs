module Skm.Compiler.Translate where

import Skm.Compiler.Ast
import qualified Skm.Ast as A

decVars :: Int -> Expr -> Expr
decVars depth (Var n)
  | n > depth = Var $ n - 1
  | otherwise = Var n
decVars depth (Call lhs rhs) = Call (decVars depth lhs) (decVars depth rhs)
decVars depth (Lam bty bdy)  = Lam  (decVars (depth + 1) bty) (decVars (depth + 1) body)
decVars x = x

-- Attempts to remove as many lambda abstractions as possible
lift :: Expr -> Expr
lift (Call lhs rhs)           = (Call (lift lhs) (lift rhs))
lift (Lam bty (Call lhs rhs)) = lift (Call (Call S lhs') rhs')
  where lhs' = Lam bty (lift lhs)
        rhs' = Lam bty (lift rhs)
lift (Lam bty (Var 0))           = (Call (Call S K) K)
lift (Lam bty0 (Lam bty1 body))  = lift (Lam bty0' body')
  where
    bty0' = lift bty0
    bty1' = lift bty1
    body' = lift (Lam bty1' body)
lift (Lam x) = lift (Call K x')
  where x' = (decVars 0 . lift) x
lift e = e

toSk :: Expr -> Maybe A.Expr
toSk (Call lhs rhs) = do
  lhs' <- toSk lhs
  rhs' <- toSk rhs
  (Call lhs' rhs')
toSk S = A.S
toSk K = A.K
toSk M = A.M
