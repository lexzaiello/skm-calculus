module Skm.Compiler.Translate where

import Text.Printf
import Skm.Compiler.Ast
import qualified Skm.Ast as A
import Skm.Compiler.Ast (Ctx, CompilationError, CompilationError(..))

shiftDownFrom :: Int -> Expr -> Expr
shiftDownFrom j (Var i)
  | i > j     = Var (i - 1)
  | otherwise = Var i
shiftDownFrom j (App a b) = App (shiftDownFrom j a) (shiftDownFrom j b)
shiftDownFrom j (Lam s e) = Lam s (shiftDownFrom (j + 1) e)
shiftDownFrom _ x = x

abstract :: Int -> Expr -> Expr
abstract j (Var i)
  | i == j    = App (App S K) K
  | otherwise = App K (Var (if i > j then i - 1 else i))
abstract j (App m n) = App (App S (abstract j m)) (abstract j n)
abstract j e         = App K (shiftDownFrom j e)

lift :: Expr -> Either CompilationError Expr
lift e = go [e] 0 e
  where
    go :: Ctx -> Int -> Expr -> Either CompilationError Expr
    go ctx lvl e@(Lam _ body) = do
      body' <- go (e:ctx) (lvl + 1) body

      pure $ abstract lvl body'
    go ctx lvl (App f x)    = do
      lhs <- go ctx lvl f
      rhs <- go ctx lvl x

      pure $ App lhs rhs
    go ctx _ S              = pure S
    go ctx _ K              = pure K
    go ctx _ M              = pure M
    go ctx _ (Var i)        = Left $ VariableInOutput { ctx = ctx
                                                      , i = i }

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
