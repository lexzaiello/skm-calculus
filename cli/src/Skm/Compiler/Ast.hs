{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Skm.Compiler.Ast where

import Data.List (intercalate, elemIndex)
import Text.Read (readMaybe)
import Text.Printf

type Ident       = Text
type NamedVar    = Ident
type DeBruijnVar = Int

data Binderless = Binderless

instance Show Binderless where
  show _ = ""

data OptionalTy tTy = Maybe tTy

instance (Show tTy) => Show (OptionalTy tTy) where
  show (Just t) = show t
  show Nothing  = ""

-- Calculus of constructions expr using De bruijn
-- or named indices
data ExprCoc tBinder tVar = Lam tBinder (OptionalTy $ ExprCoc tBinder tVar) Expr
  | Fall binder (Maybe ExprCoc) Expr
  | Var tVar
  | App ExprCoc ExprCoc
  | S
  | K
  | M
  deriving (Eq, Ord)

type HumanReadableExprCoc = ExprCoc NamedVar NamedVar
type DebruijnExprCoc      = ExprCoc Binderless DebruijnVar

type Ctx tBinder tVar = [ExprCoc tBinder tVar]

data CompilationError tBinder tVar =
  DebruijnFailed { ctx  :: NamedContext
                 , v    :: String }
  | UnknownConst { ctx  :: ExprCoc tBinder tVar
                 , cnst :: String }

type CompilationResult = Either CompilationError a

instance Show CompilationError where
  show err = (case err of
    (DebruijnFailed { ctx = ctx, v = v }) ->
      printf "failed to convert human-readable variable to debruijn %s in context %s" (show i) (show ctx)
    (UnknownConst { ctx = ctx, cnst = cntx }) ->
      printf "encountered an unknown constant %s in expr %s" cnst (show cxt))

-- Convert variables under a binder to de bruijn indices
changeVariables :: Ctx NamedVar -> ExprCoc NamedVar NamedVar -> CompilationResult (ExprCoc Binderless DeBruijnVar)
changeVariables ctx (Fall binder maybeTy body) = Fall () (doChange <$> maybeTy) (doChange body)
  where doChange = changeVariables (binder : ctx)
changeVariables ctx (Lam binder maybeTy body)  = Lam ()  (doChange <$> maybeTy) (doChange body)
  where doChange = changeVariables (binder : ctx)
changeVariables ctx  (Var v) = case elemIndex v ctx of
  Just ix -> pure $ Var ix
  Nothing -> Left $ DebruijnFailed { ctx = ctx, v = v }
changeVariables ctx (App lhs rhs) = do
  lhs' <- changeVariables ctx lhs
  rhs' <- changeVariables ctx rhs

  pure $ App lhs' rhs'
changeVariables _ e = pure e

data Stmt tExpr = Def Ident tExpr

type Program tStmt tBody = ([Stmt tStmt], Maybe tBody)

instance (Show tBinder) => (Show tVar) => Show (ExprCoc tBinder tVar) where
  show (Lam  binder (Just bindTy) body) = printf "λ (%s : %s) => %s" (show binder) (show bindTy) (show body)
  show (Fall binder (Just bindTy) body) = printf "∀ (%s : %s), %s"   (show binder) (show bindTy) (show body)
  show S                         = "S"
  show K                         = "K"
  show M                         = "M"
  show (App lhs rhs)             = printf "(%s %s)" (show lhs) (show rhs)
  show (Var v)                   = show v

instance (Show a) => Show (Stmt a) where
  show (Def name value) = printf "def %s := %s" name (show value)

fromHumanExprCoc :: ExprCoc NamedVar NamedVar -> CompilationResult (ExprCoc Binderless DebruijnVar)
fromHumanExprCoc e
  where go :: NamedContext -> CompilationResult (ExprCoc Binderless DebruijnVar)
        go _ S             = pure S
        go _ K             = pure K
        go _ M             = pure M
        go binders (Var n) = Left $ DebruijnFailed
                               { ctx = binders
                               , v = n })
        readMaybe n
        go ctx (App lhs rhs) = do
          lhs' <- go ctx lhs
          rhs' <- go ctx rhs

          pure $ App lhs' rhs'
        go ctx (Lam binder maybeTy body) = do
          (ty', body') <- goAbstr ctx binder maybeTy body
          pure $ Lam Binderless ty' body'
        go ctx (Fall binder maybeTy body) = do
          (ty', body') <- goAbstr ctx binder maybeTy body
          pure $ Fall Binderless ty' body'
        goAbstr ctx binder maybeTy body =
          let ty'   = changeVariables [binder] <$> maybeTy
              body' = changeVariables [binder] body
              ctx'  = binder:ctx
          in do
            parsedBody <- go ctx' body'
            pure $ ((ty' >>= go ctx'), parsedBody)
