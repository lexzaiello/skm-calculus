{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Skm.Compiler.Ast where

import Data.Text (Text)
import Data.List (elemIndex)
import Text.Printf

type Ident       = Text
type NamedVar    = Ident
type DebruijnVar = Int

data Binderless = Binderless
  deriving (Eq, Ord)

instance Show Binderless where
  show _ = ""

newtype OptionalTy tTy = OptionalTy (Maybe tTy)
  deriving (Eq, Ord, Functor, Applicative, Monad)

instance (Show tTy) => Show (OptionalTy tTy) where
  show (OptionalTy (Just t)) = show t
  show (OptionalTy Nothing)  = ""

-- Calculus of constructions expr using De bruijn
-- or named indices
data ExprCoc tBinder tVar = Lam !tBinder !(OptionalTy (ExprCoc tBinder tVar)) !(ExprCoc tBinder tVar)
  | Fall !tBinder !(OptionalTy (ExprCoc tBinder tVar)) !(ExprCoc tBinder tVar)
  | Var !tVar
  | App !(ExprCoc tBinder tVar) !(ExprCoc tBinder tVar)
  | S
  | K
  | M
  deriving (Eq, Ord)

instance Functor (ExprCoc tBinder) where
  fmap f (App lhs rhs) = App (fmap f lhs) (fmap f rhs)
  fmap f (Lam binder  bindTy body) = Lam binder (fmap f <$> bindTy) (fmap f body)
  fmap f (Fall binder bindTy body) = Fall binder (fmap f <$> bindTy) (fmap f body)
  fmap f (Var x) = Var $ f x
  fmap _ S = S
  fmap _ K = K
  fmap _ M = M

type HumanReadableExprCoc = ExprCoc NamedVar NamedVar
type DebruijnExprCoc      = ExprCoc Binderless DebruijnVar

type Ctx tBinder = [tBinder]

type ParseError = String
type ParseResult a = Either ParseError a

parseResultToCompilationResult :: ParseResult a -> CompilationResult a
parseResultToCompilationResult = either (Left . ParseFailure) Right

data CompilationError =
  DebruijnFailed     { vCtx :: !(Ctx NamedVar)
                     , v    :: !Ident }
  | UnknownConst !Ident
  | VariableInOutput { dCtx :: !(Ctx DebruijnExprCoc)
                     , dV   :: !DebruijnVar }
  | LambdaInOutput   { e    :: !DebruijnExprCoc }
  | ParseFailure !ParseError

type CompilationResult a = Either CompilationError a

instance Show CompilationError where
  show = \case
    (DebruijnFailed { vCtx = ctx, v = vr }) ->
      printf "failed to convert human-readable variable to debruijn %s in context %s" (show vr) (show ctx)
    (UnknownConst cn) -> printf "encountered an unknown constant %s" cn
    (VariableInOutput { dCtx = ctx, dV = d }) ->
      printf "couldn't lift the variable %s in context %s" (show d) (show ctx)
    (LambdaInOutput { e = cause }) ->
      printf "compilation produced a lambda expression in output %s" (show cause)
    ParseFailure p -> printf "parsing produced an error: %s" p

data Stmt tExpr = Def !Ident !tExpr

defBody :: Stmt tExpr -> Maybe tExpr
defBody (Def _ bdy) = Just bdy

type Program tStmt tBody = ([Stmt tStmt], Maybe tBody)

instance (Show tBinder, Show tVar) => Show (ExprCoc tBinder tVar) where
  show (Lam  binder bindTy body) = printf "λ (%s : %s) => %s" (show binder) (show bindTy) (show body)
  show (Fall binder bindTy body) = printf "∀ (%s : %s), %s"   (show binder) (show bindTy) (show body)
  show S                         = "S"
  show K                         = "K"
  show M                         = "M"
  show (App lhs rhs)             = printf "(%s %s)" (show lhs) (show rhs)
  show (Var x)                   = show x

instance (Show a) => Show (Stmt a) where
  show (Def name value) = printf "def %s := %s" name (show value)

-- Convert variables under a binder to de bruijn indices
changeVariables :: Ctx NamedVar -> HumanReadableExprCoc -> CompilationResult DebruijnExprCoc
changeVariables ctx (Fall binder maybeTy body) = do
  body' <- doChange body

  pure $ Fall Binderless (maybeTy >>= (either (const $ OptionalTy Nothing) (OptionalTy . Just) . doChange)) body'
  where doChange = changeVariables (binder : ctx)
changeVariables ctx (Lam binder maybeTy body) = do
  body' <- doChange body

  pure $ Lam Binderless (maybeTy >>= (either (const $ OptionalTy Nothing) (OptionalTy . Just) . doChange)) body'
  where doChange = changeVariables (binder : ctx)
changeVariables ctx  (Var x) = case elemIndex x ctx of
  Just ix -> pure $ Var ix
  Nothing -> Left $ DebruijnFailed { vCtx = ctx, v = x }
changeVariables ctx (App lhs rhs) = do
  lhs' <- changeVariables ctx lhs
  rhs' <- changeVariables ctx rhs

  pure $ App lhs' rhs'
changeVariables _ S = pure S
changeVariables _ K = pure K
changeVariables _ M = pure M

fromHumanExprCoc :: HumanReadableExprCoc -> CompilationResult DebruijnExprCoc
fromHumanExprCoc = go []
  where go :: Ctx NamedVar -> HumanReadableExprCoc -> CompilationResult DebruijnExprCoc
        go _ S             = pure S
        go _ K             = pure K
        go _ M             = pure M
        go binders (Var n) = Left $ DebruijnFailed
                               { vCtx = binders
                               , v = n }
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
        goAbstr _ binder maybeTy body = do
          ty'   <- maybeToEither (changeVariables [binder]) maybeTy
          body' <- changeVariables [binder] body

          pure (ty', body')
        maybeToEither _ (OptionalTy Nothing)  = Right (OptionalTy Nothing)
        maybeToEither f (OptionalTy (Just a)) = fmap (OptionalTy . Just) (f a)

