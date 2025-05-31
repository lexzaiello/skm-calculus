/-
I define strong normalization inductively as:

- Termination in one step of evaluation
- Strong normalization of the next step of evaluation
-/

import SkLean.Ast
import SkLean.Dsl
import SkLean.Typing

open SkExpr

inductive Sn : SkExpr → Prop
  | trivial (call : Call) : eval_once call = (.call call) → Sn (.call call)
  | hard    (call : Call) : (Sn ∘ eval_once) call → Sn (.call call)

/-
I reuse the [previous lemmas](./SnLc.lean.md) about SN bidirectionality.
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
