import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Error

open Dsl

namespace Dsl

abbrev DebruijnIndex := ℕ

inductive ExprCoc (binder : Type) (var : Type) where
  | sk   : Ast.Expr → ExprCoc binder var
  | forE : binder
    → ExprCoc binder var
    → ExprCoc binder var
    → ExprCoc binder var
  | lam  : binder
    → ExprCoc binder var
    → ExprCoc binder var
    → ExprCoc binder var
  | app  : ExprCoc binder var
    → ExprCoc binder var
    → ExprCoc binder var
  | var : var → ExprCoc binder var
deriving BEq, Repr, Lean.ToExpr

declare_syntax_cat exprcoc
declare_syntax_cat appcoc
declare_syntax_cat atomcoc
declare_syntax_cat binder
declare_syntax_cat judgmentcoc

syntax "(" ident ":" exprcoc ")"   : binder
syntax ident ":" exprcoc           : binder
syntax "(" exprcoc ":" exprcoc ")" : judgmentcoc

syntax ident           : atomcoc
syntax judgmentcoc     : atomcoc
syntax "(" exprcoc ")" : atomcoc

syntax appcoc atomcoc : appcoc
syntax appcoc atom    : appcoc
syntax atomcoc        : appcoc
syntax atom           : appcoc

syntax appcoc                                      : exprcoc
syntax "λ" binder binder* "=>" exprcoc             : exprcoc
syntax "∀" binder* "," exprcoc                     : exprcoc

syntax "c⟪" exprcoc "⟫"  : term
syntax "c⟪₀" atomcoc "⟫" : term
syntax "c⟪₁" appcoc "⟫"  : term

macro_rules
  | `(c⟪₁ $e:atom ⟫) => `(@ExprCoc.sk Unit DebruijnIndex ⟪₀ $e⟫)
  | `(c⟪₀ ($e:exprcoc)⟫) => `(c⟪$e⟫)
  | `(c⟪ $e:atomcoc ⟫) => `(c⟪₀ $e ⟫)
  | `(c⟪ $e:appcoc ⟫) => `(c⟪₁ $e⟫)
  | `(c⟪₁ $e:atomcoc ⟫) => `(c⟪₀ $e⟫)

namespace ExprCoc

end ExprCoc

end Dsl
