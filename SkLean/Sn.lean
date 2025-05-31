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
  | trivial e : eval_once e = e    → Sn e
  | hard    e : (Sn ∘ eval_once) e → Sn e

/-
I reuse the [previous lemmas](./SnLc.lean.md) about SN bidirectionality.
-/

lemma eval_rfl_imp_sn_iff : ∀ e, eval_once e = e → (Sn (eval_once e) ↔ Sn e) := by
  intro e h_eq
  constructor
  rw [h_eq]
  simp
  rw [h_eq]
  simp

lemma sn_bidirectional : ∀ (e : SkExpr), Sn (eval_once e) ↔ Sn e := by
  intro e
  match e with
    | .var n =>
      have h : eval_once (.var n) = (.var n) := by
        unfold eval_once
        simp
      apply eval_rfl_imp_sn_iff
      exact h
    | .call lhs rhs =>
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
    | .k =>
      have h : eval_once k = k := by
        unfold eval_once
        simp
      apply eval_rfl_imp_sn_iff
      exact h
    | .s =>
      have h : eval_once s = s := by
        unfold eval_once
        simp
      apply eval_rfl_imp_sn_iff
      exact h
    | .fall a b =>
      have h : eval_once (fall a b) = fall a b := by
        unfold eval_once
        simp
      apply eval_rfl_imp_sn_iff
      exact h
    | .prp =>
      have h : eval_once prp = prp := by
        unfold eval_once
        simp
      apply eval_rfl_imp_sn_iff
      exact h
    | .ty n =>
      have h : eval_once (ty n) = ty n := by
        unfold eval_once
        simp
      apply eval_rfl_imp_sn_iff
      exact h
