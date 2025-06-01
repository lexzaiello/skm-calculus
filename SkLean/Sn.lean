/-
# Strong Normalization Definition

I define strong normalization inductively as:

- Termination in one step of evaluation
- Strong normalization of the next step of evaluation

I assume strong normalization of terms that are not evaluatable (e.g., Prop, Ty, etc.).
Unsubstituted variables are assumed to be strongly normalizing, as the inductive definition of Sn for call evaluation does not produce unsubstituted variables (except free variables, which are also strongly normalizing).
-/

import SkLean.Ast
import SkLean.Dsl
import SkLean.Typing

open SkExpr

inductive Sn : SkExpr → Prop
  | trivial (call : Call) : eval_once call = (.call call) → Sn (.call call)
  | hard    (call : Call) : (Sn ∘ eval_once) call → Sn (.call call)
  | prp     (prp  : Prp)  : Sn (.prp prp)
  | ty      (t    : Ty)   : Sn (.ty t)
  | fall    (f    : Fall) : Sn (.fall f)
  | var     (v    : Var)  : Sn (.var v)

/-
I reuse the [previous lemmas](./SnLc.lean.md) about SN bidirectionality (preservation of SN).
-/

lemma eval_rfl_imp_sn_iff : ∀ (call : Call), eval_once call = (.call call) → (Sn (eval_once call) ↔ Sn (.call call)) := by
  intro e h_eq
  constructor
  rw [h_eq]
  simp
  rw [h_eq]
  simp

lemma sn_bidirectional : ∀ (call : Call), Sn (eval_once call) ↔ Sn (.call call) := by
  intro e
  constructor
  intro h
  apply Sn.hard
  exact h
  intro h
  cases h
  case mpr.trivial a =>
    rw [a]
    apply Sn.trivial
    exact a
  case mpr.hard a =>
    exact a

/-
We thus define our primary theorem as such. In the following chapters, I prove this statement by defining reducibility candidiates, proving all well-typed expressions are composable of reducibility candidates, and that all reducibility candidate are strongly normalizing.
-/

def all_well_typed_sn (ctx : Ctx) := ∀ (e : SkExpr) (t : SkExpr), valid_judgement ctx e t → Sn e
