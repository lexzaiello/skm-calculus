module Skm.Compiler.Translate where

import Skm.Ast (SkExpr (..))
import qualified Skm.Ast as SkmAst
import Skm.Compiler.Ast (DebruijnVar, Binderless(..), DebruijnExprCoc, ExprCoc(..), Ctx, CompilationError, CompilationError(..), CompilationResult)
import qualified Skm.Compiler.Ast as CAst

allSk :: TransExpr -> Bool
allSk HumanS = True
allSk HumanK = True
allSk HumanM = True
allSk (TApp lhs rhs) = allSk lhs && allSk rhs
allSk _ = False

data TransExpr = TLam TransExpr
  | TVar DebruijnVar
  | TApp TransExpr TransExpr
  | HumanS
  | HumanK
  | HumanM
  | TranslationS
  | TranslationK
  | TranslationM
  deriving (Eq, Ord)


shiftDownFrom :: Int -> TransExpr -> TransExpr
shiftDownFrom j (TVar i)
  | i > j     = TVar (i - 1)
  | otherwise = TVar i
shiftDownFrom j (TApp a b) = TApp (shiftDownFrom j a) (shiftDownFrom j b)
shiftDownFrom j (TLam e)   = TLam (shiftDownFrom (j + 1) e)
shiftDownFrom _ x = x

freeIn :: Int -> TransExpr -> Bool
freeIn j (TVar i)    = i == j
freeIn j (TApp f x)  = freeIn j f || freeIn j x
freeIn j (TLam body) = freeIn (j + 1) body
freeIn _ _           = False

abstract :: Int -> TransExpr -> TransExpr
abstract j (TApp f (TVar i))
  | i == j && not (freeIn j f) = shiftDownFrom j f
abstract j (TVar i)
  | i == j    = TApp (TApp TranslationS TranslationK) TranslationK
  | otherwise = TApp TranslationK (TVar (if i > j then i - 1 else i))
abstract j e@(TApp m n)
  | allSk e = e
  | otherwise = TApp (TApp TranslationS (abstract j m)) (abstract j n)
abstract j e
  | allSk e = e
  | otherwise = TApp TranslationK (shiftDownFrom j e)

-- TODO: Better error handling here
toTransExpr :: DebruijnExprCoc -> TransExpr
toTransExpr CAst.S         = HumanS
toTransExpr CAst.K         = HumanK
toTransExpr CAst.M         = HumanM
toTransExpr (App lhs rhs)  = TApp (toTransExpr lhs) (toTransExpr rhs)
toTransExpr (Lam _ _ body) = TLam (toTransExpr body)
toTransExpr (Var v)        = TVar v

transExprToExprCoc :: TransExpr -> DebruijnExprCoc
transExprToExprCoc HumanS        = CAst.S
transExprToExprCoc HumanK        = CAst.K
transExprToExprCoc HumanM        = CAst.M
transExprToExprCoc TranslationS  = CAst.S
transExprToExprCoc TranslationK  = CAst.K
transExprToExprCoc TranslationM  = CAst.M
transExprToExprCoc (TApp lhs rhs) = App (transExprToExprCoc lhs) (transExprToExprCoc rhs)

lift :: DebruijnExprCoc -> CompilationResult DebruijnExprCoc
lift e = transExprToExprCoc <$> go [toTransExpr e] 0 (toTransExpr e)
  where
    go :: Ctx TransExpr -> Int -> TransExpr -> Either CompilationError TransExpr
    go ctx lvl e@(TLam body) = do
      body' <- go (e:ctx) (lvl + 1) body

      pure $ abstract 0 body'
    go ctx lvl (TApp f x)    = do
      lhs <- go ctx lvl f
      rhs <- go ctx lvl x

      pure $ TApp lhs rhs
    go _ _ HumanS  = pure HumanS
    go _ _ HumanK  = pure HumanK
    go _ _ HumanM  = pure HumanM
    go _ _ TranslationS  = pure TranslationS
    go _ _ TranslationK  = pure TranslationK
    go _ _ TranslationM  = pure TranslationM
    go _ _ (TVar i) = pure (TVar i)

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
