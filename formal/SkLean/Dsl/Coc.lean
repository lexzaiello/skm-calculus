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
  | var  : var → ExprCoc binder var
  | hole : ExprCoc binder var
deriving BEq, Repr, Lean.ToExpr

declare_syntax_cat exprcoc
declare_syntax_cat appcoc
declare_syntax_cat atomcoc
declare_syntax_cat binder
declare_syntax_cat judgmentcoc
declare_syntax_cat arrowcoc

syntax "(" ident ":" exprcoc ")" : binder
syntax ident ":" atomcoc         : binder
syntax "(" "_" ":" exprcoc ")" : binder
syntax "_" ":" atomcoc         : binder
syntax "(" exprcoc ":" exprcoc ")" : judgmentcoc

syntax ident           : atomcoc
syntax judgmentcoc     : atomcoc
syntax "(" exprcoc ")" : atomcoc
syntax "?"             : atomcoc

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
  | `(c⟪ $t_in:atomcoc ⤳ $t_out:exprcoc ⟫) => `(ExprCoc.app c⟪₁ (#~>) $t_in ⟫ c⟪ $t_out ⟫)
  | `(c⟪ $t_out:exprcoc <~ $t_in:atomcoc ⟫) => `(ExprCoc.app c⟪₁ (#~>) $t_in ⟫ c⟪ $t_out ⟫)
  | `(c⟪ $t_in:atomcoc → $t_out:exprcoc ⟫)  => `(ExprCoc.app c⟪₁ (#->) $t_in ⟫ c⟪ $t_out ⟫)
  | `(c⟪ $t_out:exprcoc ← $t_in:atomcoc ⟫)  => `(ExprCoc.app c⟪₁ (#->) $t_in ⟫ c⟪ $t_out ⟫)
  | `(c⟪₀ ($e:atom)⟫) => `(ExprCoc.sk ⟪₀ $e⟫)
  | `(c⟪₀ ($e:app)⟫) => `(ExprCoc.sk ⟪₁ $e⟫)
  | `(c⟪₀ ($e:exprcoc)⟫) => `(c⟪$e⟫)
  | `(c⟪₀ ?⟫) => `(ExprCoc.hole)
  | `(c⟪ $e:app ⟫) => `(ExprCoc.sk ⟪₁ $e⟫)
  | `(c⟪ $e:atomcoc ⟫) => `(c⟪₀ $e ⟫)
  | `(c⟪ $e:appcoc ⟫) => `(c⟪₁ $e⟫)
  | `(c⟪₁ $e₁:appcoc $e₂:atomcoc ⟫) => `(ExprCoc.app c⟪₁ $e₁⟫ c⟪₀ $e₂⟫)
  | `(c⟪₁ $e:atomcoc ⟫) => `(c⟪₀ $e⟫)
  | `(c⟪₀ $i:ident ⟫) =>
    let si := Lean.Syntax.mkStrLit (i.getId.toString)
    `(@ExprCoc.var String String $si)
  | `(c⟪ ∀ $v:ident : ($t:exprcoc), $body:exprcoc ⟫) => `(c⟪ ∀ ($v : $t), $body ⟫)
  | `(c⟪ ∀ _ : ($t:exprcoc), $body:exprcoc ⟫) => `(c⟪ ∀ (_ : $t), $body ⟫)
  | `(c⟪ ∀ (_ : $t:exprcoc), $body ⟫) =>
    `(ExprCoc.forE () c⟪ $t ⟫ c⟪ $body ⟫)
  | `(c⟪ ∀ ($v:ident : $t:exprcoc), $body ⟫) =>
    let si := Lean.Syntax.mkStrLit (v.getId.toString)
    `(ExprCoc.forE $si c⟪ $t ⟫ c⟪ $body ⟫)
  | `(c⟪ ∀ ($v:ident : $t:exprcoc) $binders*, $body ⟫) => `(c⟪ ∀ ($v : $t), ∀ $binders*, $body ⟫)
  | `(c⟪ ∀ (_ : $t:exprcoc) $binders*, $body ⟫) => `(c⟪ ∀ (_ : $t), ∀ $binders*, $body ⟫)

def ReadableExprCoc := ExprCoc String String

namespace ExprCoc

def to_debruijn (ctx : List String) : ReadableExprCoc → Except ReadableExprCoc (ExprCoc Unit DebruijnIndex)
  | e@(.var x) => match ctx.idxOf? x with
    | .some e => pure $ .var e
    | _ => .error e
  | .sk e => pure $ .sk e
  | .app lhs rhs => do
    let lhs' ← to_debruijn ctx lhs
    let rhs' ← to_debruijn ctx rhs

    pure $ .app lhs' rhs'
  | .lam b t e => do
    let ctx' := b :: ctx

    let t' ← to_debruijn ctx' t
    let e' ← to_debruijn ctx' e

    pure $ .lam () t' e'
  | .forE b t e => do
    let ctx' := b :: ctx

    let t' ← to_debruijn ctx' t
    let e' ← to_debruijn ctx' e

    pure $ .forE () t' e'
  | .hole => pure .hole

end ExprCoc

end Dsl
