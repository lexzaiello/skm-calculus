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

syntax "(" ident ":" atomcoc ")" : binder
syntax ident ":" atomcoc         : binder
syntax "(" exprcoc ":" exprcoc ")" : judgmentcoc

syntax ident           : atomcoc
syntax judgmentcoc     : atomcoc
syntax "(" exprcoc ")" : atomcoc

syntax appcoc atomcoc : appcoc
syntax atomcoc        : appcoc

syntax atomcoc "⤳" exprcoc : exprcoc
syntax exprcoc "<~" atomcoc : exprcoc
syntax atomcoc "→" exprcoc : exprcoc
syntax exprcoc "←" atomcoc : exprcoc
syntax appcoc                                      : exprcoc
syntax app                                         : exprcoc
syntax "λ" binder binder* "=>" exprcoc             : exprcoc
syntax "∀" binder* "," exprcoc                     : exprcoc

syntax "c⟪" exprcoc "⟫"   : term
syntax "c⟪₀" atomcoc "⟫"  : term
syntax "c⟪₁" appcoc "⟫"   : term

macro_rules
  | `(c⟪ $t_in:atomcoc ⤳ $t_out:exprcoc ⟫) => `(ExprCoc.app c⟪₁ (⤳) $t_in ⟫ c⟪ $t_out ⟫)
  | `(c⟪ $t_out:exprcoc <~ $t_in:atomcoc ⟫) => `(ExprCoc.app c⟪₁ (⤳) $t_in ⟫ c⟪ $t_out ⟫)
  | `(c⟪ $t_in:atomcoc → $t_out:exprcoc ⟫)  => `(ExprCoc.app c⟪₁ (→) $t_in ⟫ c⟪ $t_out ⟫)
  | `(c⟪ $t_out:exprcoc ← $t_in:atomcoc ⟫)  => `(ExprCoc.app c⟪₁ (→) $t_in ⟫ c⟪ $t_out ⟫)
  | `(c⟪₀ ($e:exprcoc)⟫) => `(c⟪$e⟫)
  | `(c⟪ $e:atomcoc ⟫) => `(c⟪₀ $e ⟫)
  | `(c⟪ $e:appcoc ⟫) => `(c⟪₁ $e⟫)
  | `(c⟪ $e:app ⟫) => `(ExprCoc.sk ⟪₁ $e⟫)
  | `(c⟪₁ $e₁:appcoc $e₂:atomcoc ⟫) => `(ExprCoc.app c⟪₁ $e₁⟫ c⟪₀ $e₂⟫)
  | `(c⟪₁ $e:atomcoc ⟫) => `(c⟪₀ $e⟫)
  | `(c⟪₀ $i:ident ⟫) =>
    let si := Lean.Syntax.mkStrLit (i.getId.toString)
    `(@ExprCoc.var String String $si)
  | `(c⟪ ∀ $v:ident : $t:atomcoc, $body:exprcoc ⟫) => `(c⟪ ∀ ($v : $t), $body ⟫)
  | `(c⟪ ∀ ($v:ident : $t:atomcoc), $body ⟫) =>
    let si := Lean.Syntax.mkStrLit (v.getId.toString)
    `(ExprCoc.forE $si c⟪₀ $t ⟫ c⟪ $body ⟫)
  | `(c⟪ ∀ ($v:ident : $t:atomcoc) $binders*, $body ⟫) => `(c⟪ ∀ ($v : $t), ∀ $binders*, $body ⟫)

def ReadableExprCoc := ExprCoc String String

namespace ExprCoc

def infer_lazy : ReadableExprCoc → Except (@TypeError ReadableExprCoc) ReadableExprCoc
  | c⟪ @K #m #n ⟫ => pure c⟪ ∀ (α : (Type #m)) (β : (Type #n)) (x : α) (y : β), α ⟫
  | c⟪ @S #m #n #o ⟫ => pure c⟪ ∀ (α : (Type #m)) (β : (Type #n)) (γ : (Type #o)) (x : (α ⤳ β ⤳ γ)) (y : (α ⤳ β)) (z : α), (α ⤳ β ⤳ γ) z (y z) ⟫
  

end ExprCoc

end Dsl
