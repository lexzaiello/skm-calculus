/-
# Ast

Using our minimal core, we may now define an AST. I additionally interpret \\(K\\) and \\(S\\) as universe-polymorphic for consistency.
-/

import Mathlib.Data.Nat.Notation

inductive Expr where
  | k   : ℕ → ℕ → Expr
  | pi  : ℕ → ℕ → Expr
  | s   : ℕ → ℕ → ℕ → Expr
  | m   : Expr → Expr
  | app : Expr → Expr → Expr
  | ty  : ℕ → Expr

/-
# DSL

For ergonomics, I define a small DSL. Universe levels can usually be inferred for \\(K\\). Thus, I define \\(K\\) and \\(@K\\) separately, where  \\(@K\\) requires explicit universe arguments and \\(K\\) infers them when type arguments are already provided.
-/

declare_syntax_cat expr

syntax "@K"                : expr
syntax "@S"                : expr
syntax "K"                 : expr
syntax "S"                 : expr
syntax "M"                 : expr
syntax "Type" term         : expr
syntax "Π"                 : expr
syntax "@Π"                : expr
syntax expr expr           : expr
syntax "(" expr ")"        : expr
syntax "#" term            : expr
syntax expr "→" expr       : expr

syntax "SK[" expr "]" : term
syntax "⟪" expr "⟫"   : term

macro_rules
  | `(SK[$e:expr]) => `(⟪ $e ⟫)

def max_universe : Expr → ℕ
  | .k m n   => max m n
  | .s m n o => max (max m n) o
  | .m e => max_universe e
  | .app lhs rhs => max (max_universe lhs) (max_universe rhs)
  | .ty n => n
  | .pi m n => max m n

macro_rules
  | `(⟪ #$e:term ⟫) => `($e)
  | `(⟪ $e₁:expr → $e₂:expr ⟫) => `(⟪ (Π $e₁) ((K $e₁) (Type (max_universe ⟪ $e₂ ⟫)) $e₂) ⟫)
  | `(⟪ Type $n ⟫) => `(Expr.ty $n)
  | `(⟪ (@K #$m:term) #$n:term ⟫) => `(Expr.k $m $n)
  | `(⟪ ((@S #$m:term) #$n:term) #$o:term ⟫) => `(Expr.s $m $n $o)
  | `(⟪ (K $α:expr) $β:expr ⟫) => `(⟪ (((@K #(max_universe ⟪ $α ⟫)) #(max_universe ⟪ $β ⟫)) $α) $β ⟫)
  | `(⟪ ((S $α:expr) $β:expr) $γ:expr ⟫) => `(⟪ (((((@S #(max_universe ⟪ $α ⟫)) #(max_universe ⟪ $β ⟫)) #(max_universe ⟪ $γ ⟫)) $α) $β) $γ ⟫)
  | `(⟪ M $e:expr ⟫) => `(Expr.m ⟪$e⟫)
  | `(⟪ (@Π #$m:term) #$n:term ⟫) => `(Expr.pi $m $n)
  | `(⟪ (Π $α:expr) $β:expr ⟫) => `(⟪ (((@Π #(max_universe ⟪ $α ⟫)) #(max_universe ⟪ $β ⟫)) $α) $β ⟫)
  | `(⟪ $e₁:expr $e₂:expr ⟫) => `(Expr.app ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)
  | `(⟪ ($e:expr) ⟫) => `(⟪ $e ⟫)

/-
In the [next chapter](./Rules.lean.md), I define rules for typing judgments and evaluation using this DSL.

-/
