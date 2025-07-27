module Skm.Compiler.Translate where

import Skm.Compiler.Ast
import qualified Skm.Ast as A

decVars :: Int -> Expr -> Expr
decVars depth (Var n)
  | n > depth = Var $ n - 1
  | otherwise = Var n
decVars depth (App lhs rhs) = App (decVars depth lhs) (decVars depth rhs)
decVars depth (Lam bty bdy) = Lam (doDec <$> bty) (doDec bdy)
  where doDec = decVars (depth + 1)
decVars _ x = x

-- Attempts to remove as many lambda abstractions as possible
lift :: Expr -> Expr
lift (App lhs rhs)           = (App (lift lhs) (lift rhs))
lift (Lam bty (App lhs rhs)) = lift (App (App S lhs') rhs')
  where lhs' = Lam bty (lift lhs)
        rhs' = Lam bty (lift rhs)
lift (Lam bty (Var 0))           = (App (App S K) K)
lift (Lam bty0 (Lam bty1 body))  = lift (Lam bty0' body')
  where
    bty0' = lift <$> bty0
    bty1' = lift <$> bty1
    body' = lift (Lam bty1' body)
lift (Lam _ x) = lift (App K x')
  where x' = (decVars 0 . lift) x
lift e = e

toSk :: Expr -> Maybe A.Expr
toSk (App lhs rhs) = do
  lhs' <- toSk lhs
  rhs' <- toSk rhs
  pure (A.Call lhs' rhs')
toSk S = pure A.S
toSk K = pure A.K
toSk M = pure A.M
