module Skm.Compiler.Translate where

import Skm.Compiler.Ast
import qualified Skm.Ast as A

abstract :: Int -> Expr -> Expr
abstract j (Var i)
  | i == j    = App (App S K) K -- I
  | otherwise = App K (Var (if i > j then i - 1 else i))
abstract j (App m n) = App (App S (abstract j m)) (abstract j n)
abstract _ e         = App K e

toCombinators :: Expr -> Expr
toCombinators = go 0
  where
    go lvl (Lam _ body) = abstract lvl (go (lvl + 1) body)
    go lvl (App f x)    = App (go lvl f) (go lvl x)
    go _ S              = S
    go _ K              = K
    go _ M              = M
    go _ (Var n)        = (Var n)

lift :: Expr -> Expr
lift = toCombinators

opt :: A.Expr -> A.Expr
opt e = e

optE :: Expr -> Expr
optE e = e

toSk :: Expr -> Maybe A.Expr
toSk (App lhs rhs) = do
  lhs' <- toSk lhs
  rhs' <- toSk rhs
  pure (A.Call lhs' rhs')
toSk S = pure A.S
toSk K = pure A.K
toSk M = pure A.M
toSk _ = Nothing
