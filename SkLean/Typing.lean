/-
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
I make use of a DSL for convenience and legibility. See [DSL](./Dsl.lean.md) for more. The types of K and S are fixed, although they are dependent on a universe level provided at the meta-level.
-/

def ty_k {m n : ℕ} := SK[∀ α : Type m, ∀ β : Type n, #α → #β → #α]
def ty_s {m n o : ℕ} := SK[∀ α : Type m, ∀ β : Type n, ∀ γ : Type o, (#α → #β → #γ) → (#α → #β) → #α → #γ]

/-
Beta equivalence is defined as equality after some sequence of evaluations. Expressions are certainly \\(=_{\beta}\\) if they are definitionally equivalent. An expression is beta equivalent to another if its one-step redux is equivalent ot the other expression. I assume symmetry and transitivity.
-/

inductive beta_eq : SkExpr → SkExpr → Prop
  | trivial e₁ e₂    : e₁ = e₂ → beta_eq e₁ e₂
  | hard    e₁ e₂    : beta_eq e₁ (eval_once e₂) → beta_eq e₁ e₂
  | symm    e₁ e₂    : beta_eq e₂ e₁ → beta_eq e₁ e₂
  | trans   e₁ e₂ e₃ : beta_eq e₁ e₂ → beta_eq e₂ e₃ → beta_eq e₁ e₃

/-
- **K** expression: `t` is a valid judgement if it is equivalent to `ty_k` at the same universe level.
- **S** expression: `t` is a valid judgement if it is equivalent to `ty_s` at the same universe level.
- **e₁ e₂** expression: `t` is a valid judgement if `t_rhs` is a valid judgement for the right hand side, `t_lhs` is a valid judgement for the left hand side of the form `∀ x : t_rhs, b`, and \\(t = b[x := rhs]\\).
- **`∀ x : bindty.body`** expression: `t` is a valid judgement if `t_body` is a valid judgement for `body` and `t = t_body`.
- **`Type n`** expression: `t` is a valid judgement if `t = ty (n + 1)`.
- **`Prop`** expression: `t` is a valid judgement if `t = ty 0`
- **`var n` expression: `t` isa  valid judgement if the the nth nearest-bound variable in the context is of type `t`.
- `t` is a valid judgement for `e` if some `t'` is beta equivalent to it, and `t'` is a valid judgement for `e`.
-/

inductive valid_judgement : Ctx → SkExpr → SkExpr → Prop
  | k ctx e t m n (h_is_k : match e with | SkExpr.k => true | _ => false) :
    t = @ty_k m n → valid_judgement ctx e t
  | s ctx e t m n o (h_is_s : match e with | SkExpr.s => true | _ => false) :
    t = @ty_s m n o → valid_judgement ctx e t
  | call ctx e t
    (lhs : SkExpr) (rhs : SkExpr)
    (t_lhs : SkExpr) (t_rhs : SkExpr)
    (h_is_call : match e with | call lhs' rhs' => lhs' = lhs ∧ rhs' = rhs | _ => false) :
      valid_judgement ctx lhs t_lhs →
      valid_judgement ctx rhs t_rhs →
      some t = (t_lhs.substitute ⟨0⟩ rhs).body →
      valid_judgement ctx e t
  | fall ctx e t bind_ty body t_body (h_is_fall : match e with | fall _ _ => true | _ => false) :
    valid_judgement (bind_ty :: ctx) body t_body →
    e = fall bind_ty body →
    t = t_body → valid_judgement ctx e t
  | obvious ctx e t : (match e with | ty n => t = ty n.succ | prp => t = ty 0 | var ⟨n + 1⟩ => ctx[n]? = some t | _ => false) → valid_judgement ctx e t
  | beta_eq ctx e t t₂ : beta_eq t t₂ → valid_judgement ctx e t₂ → valid_judgement ctx e t

/-
For testing purposes, I also encode my type inference rules in an unsafe "partial" function:
-/

partial def type_of_unsafe {m n o : ℕ} (ctx : Ctx) : SkExpr → Option SkExpr
  | ty n => some $ ty n.succ
  | var n => ctx[n.toNat - 1]?
  | prp => ty 0
  | k => @ty_k m n
  | s => @ty_s m n o
  | fall bind_ty body => @type_of_unsafe m n o (bind_ty :: ctx) body
  | call lhs rhs => do
    let t_lhs <- @type_of_unsafe m n o ctx lhs
    pure $ (t_lhs.substitute ⟨0⟩ rhs).body

