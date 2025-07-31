module Skm.Compiler.Translate where

import Skm.Ast (SkExpr (..))
import qualified Skm.Ast as SkmAst
import Skm.Compiler.Ast (Binderless(..), DebruijnExprCoc, ExprCoc(..), Ctx, CompilationError, CompilationError(..), CompilationResult)
import qualified Skm.Compiler.Ast as CAst

shiftDownFrom :: Int -> DebruijnExprCoc -> DebruijnExprCoc
shiftDownFrom j (Var i)
  | i > j     = Var (i - 1)
  | otherwise = Var i
shiftDownFrom j (App a b) = App (shiftDownFrom j a) (shiftDownFrom j b)
shiftDownFrom j (Lam Binderless s e) = Lam Binderless s (shiftDownFrom (j + 1) e)
shiftDownFrom _ x = x

abstract :: Int -> DebruijnExprCoc -> DebruijnExprCoc
abstract j (Var i)
  | i == j    = App (App CAst.S CAst.K) CAst.K
  | otherwise = App CAst.K (Var (if i > j then i - 1 else i))
abstract j (App m n) = App (App CAst.S (abstract j m)) (abstract j n)
abstract j e         = App CAst.K (shiftDownFrom j e)

lift :: DebruijnExprCoc -> CompilationResult DebruijnExprCoc
lift e = go [e] 0 e
  where
    go :: Ctx DebruijnExprCoc -> Int -> DebruijnExprCoc -> Either CompilationError DebruijnExprCoc
    go ctx lvl e@(Lam Binderless _ body) = do
      body' <- go (e:ctx) (lvl + 1) body

      pure $ abstract lvl body'
    go ctx lvl (App f x)    = do
      lhs <- go ctx lvl f
      rhs <- go ctx lvl x

      pure $ App lhs rhs
    go _ _ CAst.S  = pure CAst.S
    go _ _ CAst.K  = pure CAst.K
    go _ _ CAst.M  = pure CAst.M
    go _ _ (Var i) = pure (Var i)

toSk :: DebruijnExprCoc -> CompilationResult SkExpr
toSk CAst.S = pure SkmAst.S
toSk CAst.K = pure SkmAst.K
toSk CAst.M = pure SkmAst.M
toSk (App lhs rhs) = do
  lhs' <- toSk lhs
  rhs' <- toSk rhs

  pure $ Call lhs' rhs'
toSk e = (Left  . LambdaInOutput) e

opt :: SkExpr -> SkExpr
opt e = e
