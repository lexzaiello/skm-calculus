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

declare_syntax_cat atom
declare_syntax_cat app
declare_syntax_cat expr

syntax "@K"                : atom
syntax "@S"                : atom
syntax "K"                 : atom
syntax "S"                 : atom
syntax "M"                 : atom
syntax "Type" term         : atom
syntax "Π"                 : atom
syntax "@Π"                : atom
syntax "(" app ")"         : atom
syntax "#" term            : atom
syntax atom "→" atom       : atom

syntax app atom : app
syntax atom     : app

syntax app : expr

syntax "SK[" expr "]" : term
syntax "⟪" expr "⟫"   : term
syntax "⟪₁" atom "⟫"  : term
syntax "⟪₂" app "⟫"   : term

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
  | `(⟪₁ $e₁:atom → $e₂:atom ⟫) => `(⟪ (Π $e₁) ((K $e₁) (Type (max_universe ⟪₁ $e₂ ⟫)) $e₂) ⟫)
  | `(⟪₁ Type $n ⟫) => `(Expr.ty $n)
  | `(⟪₁ #$e:term ⟫) => `($e)
  | `(⟪₂ @K #$m:term #$n:term ⟫) => `(Expr.k $m $n)
  | `(⟪₂ @S #$m:term #$n:term #$o:term ⟫) => `(Expr.s $m $n $o)
  | `(⟪₂ K $α:atom $β:atom ⟫) => `(⟪ (@K #(max_universe ⟪₁ $α ⟫) #(max_universe ⟪₁ $β ⟫)) $α $β ⟫)
  | `(⟪₂ S $α:atom $β:atom $γ:atom ⟫) => `(⟪ ((@S #(max_universe ⟪₁ $α ⟫) #(max_universe ⟪₁ $β ⟫) #(max_universe ⟪₁ $γ ⟫))) $α $β $γ ⟫)
  | `(⟪₂ M $e:atom ⟫) => `(Expr.m ⟪₁ $e⟫)
  | `(⟪₂ @Π #$m:term #$n:term ⟫) => `(Expr.pi $m $n)
  | `(⟪₂ Π $α:atom $β:atom ⟫) => `(⟪ (((@Π #(max_universe ⟪₁ $α ⟫)) #(max_universe ⟪₁ $β ⟫)) $α) $β ⟫)
  | `(⟪ $e:atom ⟫) => `(⟪₁ $e:atom ⟫)
  | `(⟪ $e:app ⟫) => `(⟪₂ $e:app ⟫)
  | `(⟪₂ ($e:app) ⟫) => `(⟪₂ $e ⟫)
  | `(⟪₁ ($e:atom) ⟫) => `(⟪₁ $e ⟫)
  | `(⟪₂ ($e₁:app) $e₂:atom ⟫) => `(⟪₂ $e₁ $e₂ ⟫)
  | `(⟪₂ $e₁:app $e₂:atom ⟫) => `(Expr.app ⟪₂ $e₁ ⟫ ⟪₁ $e₂ ⟫)

/-
In the [next chapter](./Rules.lean.md), I define rules for typing judgments and evaluation using this DSL.

-/
