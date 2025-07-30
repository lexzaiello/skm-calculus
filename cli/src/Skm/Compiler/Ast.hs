{-# LANGUAGE DuplicateRecordFields #-}

module Skm.Compiler.Ast where

import Data.List (intercalate, elemIndex)
import Text.Read (readMaybe)
import Text.Printf

-- Calculus of constructions expr, using 0-indexed De Bruijn Indices
-- Lambda abstractions are optionally typed. Types are inferred
-- where possible.
data CocExpr = Lam (Maybe ExprCoc) Expr
  | Fall (Maybe ExprCoc) Expr
  | Var Int
  | App ExprCoc ExprCoc
  | S
  | K
  | M
  deriving (Eq, Ord)

type Ctx = [ExprCoc]
type NamedContext = [String]

data CompilationError =
  VariableInOutput { ctx :: Ctx
                   , i   :: Int }
  | DebruijnFailed { ctx :: NamedContext
                   , v   :: String }

instance Show CompilationError where
  show err = (case err of
    (VariableInOutput { ctx = ctx, i = i }) ->
      printf "unexpected variable %s in context %s" (show i) (show ctx)
    (DebruijnFailed   { ctx = ctx, v = v }) ->
      printf "failed to convert human-readable variable to debruijn %s in context %s" (show i) (show ctx))

-- Convert variables under a binder to de bruijn indices
changeVariables :: NamedContext -> HumanExprCoc -> HumanExprCoc
changeVariables ctx (HFall binder maybeTy body) = HFall binder (doChange <$> maybeTy) (doChange body)
  where doChange = changeVariables (binder : ctx)
changeVariables ctx (HLam binder maybeTy body)  = HLam binder  (doChange <$> maybeTy) (doChange body)
  where doChange = changeVariables (binder : ctx)
changeVariables ctx  (HVar v) = case elemIndex v ctx of
  Just ix -> HVar (show ix)
  Nothing -> HVar v
changeVariables ctx (HApp lhs rhs) = HApp (changeVariables ctx lhs) (changeVariables ctx rhs)
changeVariables _ e = e

-- Human readable, not used anywhere except for parsing purposes
data HumanExprCoc = HLam String (Maybe HumanExprCoc) HumanExprCoc
  | HFall String (Maybe HumanExprCoc) HumanExprCoc
  | HVar String
  | HApp HumanExprCoc HumanExprCoc
  | Hs
  | Hk
  | Hm
  deriving (Eq, Ord)

data Stmt = Def String HumanExprCoc

instance Show HumanExprCoc where
  show (HLam  binder (Just bindTy) body) = printf "λ (%s : %s) => %s" binder (show bindTy) (show body)
  show (HFall binder (Just bindTy) body) = printf "∀ (%s : %s), %s"   binder (show bindTy) (show body)
  show (HLam  binder Nothing body)       = printf "λ %s => %s"        binder (show body)
  show (HFall binder Nothing body)       = printf "∀ %s, %s"          binder (show body)
  show Hs                                = "S"
  show Hk                                = "K"
  show Hm                                = "M"
  show (HApp lhs rhs)                    = printf "(%s %s)" (show lhs) (show rhs)
  show (HVar v)                          = v

instance Show ExprCoc where
  show (Lam  (Just bindTy) body) = printf "λ ( : %s) => %s" (show bindTy) (show body)
  show (Fall (Just bindTy) body) = printf "∀ ( : %s), %s"   (show bindTy) (show body)
  show (Lam  Nothing body)       = printf "λ => %s"         (show body)
  show (Fall Nothing body)       = printf "∀, %s"           (show body)
  show S                         = "S"
  show K                         = "K"
  show M                         = "M"
  show (App lhs rhs)             = printf "(%s %s)" (show lhs) (show rhs)

  show (Var v)                   = show v

instance Show Stmt where
  show (Def name value) = printf "def %s := %s" name (show value)

fromHumanExprCoc :: HumanExprCoc -> Either CompilationError ExprCoc
fromHumanExprCoc e
  where go :: NamedContext -> Either CompilationError ExprCoc
        go _ Hs             = pure S
        go _ Hk             = pure K
        go _ Hm             = pure M
        go binders (HVar n) = maybe
          (Right . Var)
          (Left $ DebruijnFailed { ctx = binders
                                 , v = n })
        readMaybe n
        go ctx (HApp lhs rhs) = do
          lhs' <- go ctx lhs
          rhs' <- go ctx rhs

          pure $ App lhs' rhs'
        go ctx (Hlam binder maybeTy body) = do
          (ty', body') <- goAbstr ctx binder maybeTy body
          pure $ HLam ty' body'
        go ctx (HFall binder maybeTy body) = do
          (ty', body') <- goAbstr ctx binder maybeTy body
          pure $ HFall ty' body'
        goAbstr ctx binder maybeTy body =
          let ty'   = changeVariables [binder] <$> maybeTy
              body' = changeVariables [binder] body
              ctx'  = binder:ctx
          in do
            parsedBody <- go ctx' body'
            pure $ ((ty' >>= go ctx'), parsedBody)

toHumanExprCoc :: ExprCoc -> Either CompilationError HumanExprCoc
toHumanExprCoc (App lhs rhs) = do
  lhs' <- toHumanExprCoc lhs
  rhs' <- toHumanExprCoc rhs

  pure $ HApp lhs' rhs'
toHumanExprCoc S              = pure Hs
toHumanExprCoc K              = pure Hk
toHumanExprCoc M              = pure Hm
toHumanExprCoc _              = Nothing

fromHumanExprCoc :: HumanExprCoc -> Either CompilationError ExprCoc
fromHumanExprCoc (HApp lhs rhs) = do
  lhs' <- fromHumanExprCoc lhs
  rhs' <- fromHumanExprCoc rhs

  pure $ App lhs' rhs'
fromHumanExprCoc Hs              = pure S
fromHumanExprCoc Hk              = pure K
fromHumanExprCoc Hm              = pure M
fromHumanExprCoc _               = Nothing

