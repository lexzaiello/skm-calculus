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
declare_syntax_cat arrowcoc

syntax "(" ident ":" exprcoc ")"   : binder
syntax ident ":" exprcoc           : binder
syntax "(" exprcoc ":" exprcoc ")" : judgmentcoc

syntax ident           : atomcoc
syntax judgmentcoc     : atomcoc
syntax "(" exprcoc ")" : atomcoc

syntax appcoc atomcoc : appcoc
syntax atomcoc        : appcoc

syntax atomcoc : arrowcoc
syntax atomcoc "⤳" arrowcoc : arrowcoc
syntax arrowcoc "<~" atomcoc : arrowcoc
syntax atomcoc "→" arrowcoc : arrowcoc
syntax arrowcoc "←" atomcoc : arrowcoc

syntax arrowcoc:max                                : exprcoc
syntax appcoc                                      : exprcoc
syntax app                                         : exprcoc
syntax "λ" binder binder* "=>" exprcoc             : exprcoc
syntax "∀" binder* "," exprcoc                     : exprcoc

syntax "c⟪" exprcoc "⟫"   : term
syntax "c⟪₀" atomcoc "⟫"  : term
syntax "c⟪₁" appcoc "⟫"   : term
syntax "c⟪₂" arrowcoc "⟫" : term

macro_rules
  | `(c⟪ $e:atom ⟫)      => `(⟪₀ $e ⟫)
  | `(c⟪ $e:arrowcoc ⟫) => `(c⟪₂ $e ⟫)
  | `(c⟪₂ $e:atomcoc ⟫) => `(c⟪₀ $e ⟫)
  | `(c⟪₂ $t_in:atomcoc ⤳ $t_out:arrowcoc ⟫) => `(c⟪₁ (⤳) $t_in (#(c⟪₂ $t_out ⟫)) ⟫)
  | `(c⟪₂ $t_out:arrowcoc <~ $t_in:atomcoc ⟫) => `(c⟪₁ (⤳) $t_in (#(c⟪₂ $t_out ⟫)) ⟫)
  | `(c⟪₂ $t_in:atomcoc → $t_out:arrowcoc ⟫)  => `(c⟪₁ (→) $t_in (#(c⟪₂ $t_out ⟫)) ⟫)
  | `(c⟪₂ $t_out:arrowcoc ← $t_in:atomcoc ⟫)  => `(c⟪₁ (→) $t_in (#(c⟪₂ $t_out ⟫)) ⟫)
  | `(c⟪ $e:app ⟫) => `(@ExprCoc.sk Unit DebruijnIndex ⟪₁ $e⟫)
  | `(c⟪₀ ($e:exprcoc)⟫) => `(c⟪$e⟫)
  | `(c⟪ $e:atomcoc ⟫) => `(c⟪₀ $e ⟫)
  | `(c⟪ $e:appcoc ⟫) => `(c⟪₁ $e⟫)
  | `(c⟪₁ $e:atomcoc ⟫) => `(c⟪₀ $e⟫)
  | `(c⟪₀ $i:ident ⟫) => `($i)
  | `(c⟪₁ $e₁:appcoc $e₂:atomcoc ⟫) => `(ExprCoc.app c⟪₁ $e₁⟫ c⟪₀ $e₂⟫)

def ReadableExprCoc := ExprCoc String String

namespace ExprCoc

#eval c⟪ K (Type #0) (Type #0) ⟫

def infer_lazy : (ExprCoc Unit DebruijnIndex) → Except (@TypeError $ ExprCoc Unit DebruijnIndex) (ExprCoc Unit DebruijnIndex)
  | c⟪ @K m n α β ⟫ => pure 

end ExprCoc

end Dsl
