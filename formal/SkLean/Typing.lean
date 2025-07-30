/-
# Type Inference

Type judgements are relatively obvious, except in the case of application, and the \\(\forall\\) expresion.

I make use of a De Bruijn-indexed context corresponding to the bound type of a variable \\(n\\) in an expression.
Indexes are offset by one. `BindId` 1 refers to the current \\(\forall\\) expression, while `ctx[0]` refers to the most recent bound variable's type.
-/

import SkLean.Ast
import SkLean.Dsl
import Mathlib.Tactic

open SkExpr

abbrev Ctx := List SkExpr

/-
I make use of a DSL for convenience and legibility. See [DSL](./Dsl.lean.md) for more. The types of K and S are fixed, although they are dependent on a universe level provided at the meta-level. It is not immediately clear that type universes are required. I plan on elaborating more in the [dependent typing examples](./DependentExamples.lean.md) chapter.
-/

def ty_k {m n : ℕ} := SK[∀ α : Type m, ∀ β : Type n, #α → #β → #α]
def ty_k_fall {m n : ℕ} := (Fall.mk (.ty (.mk m)) (.fall (Fall.mk (.ty (.mk n)) (.fall (Fall.mk (.var (.mk ⟨3⟩)) (.fall (Fall.mk (.var (.mk ⟨3⟩)) (.var (.mk ⟨4⟩)))))))))

lemma ty_k_def_eq {m n : ℕ} : @ty_k m n = (.fall (@ty_k_fall m n)) :=
  rfl

def ty_s {m n o : ℕ} := SK[∀ α : Type m, ∀ β : Type n, ∀ γ : Type o, (#α → #β → #γ) → (#α → #β) → #α → #γ]

/-

## Closedness

Note that this typing of the \\(S\\) and \\(K\\) combinators implies that **free variables are inexpressible in this calculus**. This simplifies typing judgements significantly. I prove this in the [preservation chapter](./Preservation.lean.md). I still make use of a context for a readable typing judgement.

Beta equivalence is defined as equality after some sequence of evaluations. Expressions are certainly \\(=_{\beta}\\) if they are definitionally equivalent. An expression is beta equivalent to another if its one-step redux is beta-equivalent to the other expression. I assume symmetry and transitivity.
-/

inductive beta_eq : SkExpr → SkExpr → Prop
  | trivial e₁ e₂    : e₁ = e₂ → beta_eq e₁ e₂
  | hard    e₁ e₂    : beta_eq e₁ (e₂.eval_once) → beta_eq e₁ (.call e₂)
  | symm    e₁ e₂    : beta_eq e₂ e₁ → beta_eq e₁ e₂
  | trans   e₁ e₂ e₃ : beta_eq e₁ e₂ → beta_eq e₂ e₃ → beta_eq e₁ e₃

/-
- **K** expression: `t` is a valid judgement if it is equivalent to `ty_k` at the same universe level.
- **S** expression: `t` is a valid judgement if it is equivalent to `ty_s` at the same universe level.
- **e₁ e₂** expression: `t` is a valid judgement if `t_rhs` is a valid judgement for the right hand side, `t_lhs` is a valid judgement for the left hand side of the form `∀ x : t_rhs, b`, and \\(t = b[x := rhs]\\) under some context.
- **`∀ x : bindty.body`** expression: `t` is a valid judgement if `t_body` is a valid judgement for `body` and `t = t_body`.
- **`Type n`** expression: `t` is a valid judgement if `t = ty (n + 1)`.
- **`Prop`** expression: `t` is a valid judgement if `t = ty 0`
- **`var n`** expression: `t` is a valid judgement if the the nth nearest-bound variable in the context is of type `t`.
- `t` is a valid judgement for `e` if some `t'` is beta equivalent to it, and `t'` is a valid judgement for `e`.
-/

-- valid_judgement e t
inductive valid_judgement : Ctx → SkExpr → SkExpr → Prop
  | k ctx k m n : valid_judgement ctx (.k k) (@ty_k m n)
  | s ctx s m n o : valid_judgement ctx (.s s) (@ty_s m n o)
  | call ctx (call : Call)
    (t_lhs : Fall) :
      valid_judgement ctx call.lhs (.fall t_lhs) →
      valid_judgement ctx call.rhs (t_lhs.bind_ty) →
      valid_judgement ctx (.call call) (t_lhs.substitute call.rhs).body
  | fall ctx (fall : Fall) t_bind_ty t_body :
    valid_judgement (fall.bind_ty :: ctx) fall.bind_ty t_bind_ty →
    valid_judgement (fall.bind_ty :: ctx) fall.body t_body →
    valid_judgement ctx (.fall fall) t_body
  | ty ctx (ty_e : Ty) : valid_judgement ctx (.ty ty_e) (.ty (.mk ty_e.n.succ))
  | prp ctx (prp : Prp) : valid_judgement ctx (.prp prp) (.ty (.mk 0))
  | beta_eq ctx e t t₂ : beta_eq t t₂ → valid_judgement ctx e t₂ → valid_judgement ctx e t
  | var ctx n (h_pos : n > ⟨0⟩) (h_in_bounds : (n.toNat - 1) < ctx.length) : valid_judgement ctx (.var (.mk n)) (ctx[n.toNat - 1])
