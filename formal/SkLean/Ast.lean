/-
# Ast

Using our minimal core, we may now define an AST. I additionally interpret \\(K\\) and \\(S\\) as universe-polymorphic for consistency.
-/

inductive Expr where
  | k   : ℕ → ℕ → Expr
  | s   : ℕ → ℕ → ℕ → Expr
  | m   : Expr → Expr
  | app : Expr → Expr → Expr
  | ty  : ℕ → Expr

/-

-/
