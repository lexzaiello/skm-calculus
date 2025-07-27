module Skm.Compiler.Ast where

import Data.List (intercalate)
import Text.Read (readMaybe)
import Text.Printf

-- Calculus of constructions expr, using 0-indexed De Bruijn Indices
-- Lambda abstractions are optionally typed. Types are inferred
-- where possible.
data Expr = Lam (Maybe Expr) Expr
  | Fall (Maybe Expr) Expr
  | Var Int
  | App Expr Expr
  | S
  | K
  | M
  deriving (Eq, Ord)

-- Convert variables to de bruijn indices
changeVariables :: String -> Int -> ReadableExpr -> ReadableExpr
changeVariables fromV toV (HFall binder maybeTy body) = HFall binder (doChange <$> maybeTy) (doChange body)
  where doChange = changeVariables fromV (toV + 1)
changeVariables fromV toV (HLam binder maybeTy body)  = HLam binder  (doChange <$> maybeTy) (doChange body)
  where doChange = changeVariables fromV (toV + 1)
changeVariables fromV toV  (HVar v)
  | v == fromV = HVar $ show toV
  | otherwise  = HVar v
changeVariables _ _ e = e

parseReadableExpr :: ReadableExpr -> Maybe Expr
parseReadableExpr Hs             = pure S
parseReadableExpr Hk             = pure K
parseReadableExpr Hm             = pure M
parseReadableExpr (HVar n)       = Var <$> readMaybe n
parseReadableExpr (HApp lhs rhs) = do
  lhs' <- parseReadableExpr lhs
  rhs' <- parseReadableExpr rhs

  pure $ App lhs' rhs'
parseReadableExpr (HLam binder maybeTy body) =
  let ty'   = changeVariables binder 0 <$> maybeTy
      body' = changeVariables binder 0 body
  in do
    parsedBody <- parseReadableExpr body'
    pure $ Lam (ty' >>= parseReadableExpr) parsedBody
parseReadableExpr (HFall binder maybeTy body) =
  let ty'   = changeVariables binder 0 <$> maybeTy
      body' = changeVariables binder 0 body
  in do
    parsedBody <- parseReadableExpr body'
    pure $ Fall (ty' >>= parseReadableExpr) parsedBody

-- Human readable, not used anywhere except for serialization purposes
data ReadableExpr = HLam String (Maybe ReadableExpr) ReadableExpr
  | HFall String (Maybe ReadableExpr) ReadableExpr
  | HVar String
  | HApp ReadableExpr ReadableExpr
  | Hs
  | Hk
  | Hm
  deriving (Eq, Ord)

instance Show ReadableExpr where
  show (HLam  binder (Just bindTy) body) = printf "λ (%s : %s) => %s" binder (show bindTy) (show body)
  show (HFall binder (Just bindTy) body) = printf "∀ (%s : %s), %s"   binder (show bindTy) (show body)
  show (HLam  binder Nothing body)       = printf "λ %s => %s"        binder (show body)
  show (HFall binder Nothing body)       = printf "∀ %s, %s"          binder (show body)
  show Hs                                = "S"
  show Hk                                = "K"
  show Hm                                = "M"
  show (HApp lhs rhs)                    = printf "(%s %s)" (show lhs) (show rhs)
  show (HVar v)                          = v

instance Show Expr where
  show (Lam  (Just bindTy) body) = printf "λ ( : %s) => %s" (show bindTy) (show body)
  show (Fall (Just bindTy) body) = printf "∀ ( : %s), %s"   (show bindTy) (show body)
  show (Lam  Nothing body)       = printf "λ => %s"         (show body)
  show (Fall Nothing body)       = printf "∀, %s"           (show body)
  show S                         = "S"
  show K                         = "K"
  show M                         = "M"
  show (App lhs rhs)             = printf "(%s %s)" (show lhs) (show rhs)

  show (Var v)                   = show v
