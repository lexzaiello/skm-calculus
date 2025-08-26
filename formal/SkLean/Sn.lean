import SkLean.Ast3

def sn (e : Expr) : Prop := Acc (λ e' e => is_eval_once e e') e

syntax (name := do_stuck) "do_stuck " : tactic

macro_rules
  | `(tactic| do_stuck) =>
    `(tactic| apply Acc.intro; intro e h_step; contradiction)

namespace sn

@[simp]
lemma k : sn SKM[K] := by
  do_stuck

@[simp]
lemma s : sn SKM[S] := by
  do_stuck

@[simp]
lemma m : sn SKM[M] := by
  do_stuck

lemma preserved : sn e → is_eval_once e e' → sn e' := by
  intro h_sn h_eval
  induction h_sn
  case intro x ih₁ ih₂ =>
    exact ih₁ _ h_eval

lemma intro (h : ∀ e', is_eval_once e e' → sn e') : sn e :=
  Acc.intro e h

end sn

lemma is_value_sn (h_v : is_value e) : sn e := by
  cases h_v
  repeat do_stuck

inductive is_candidate_for_ty : Expr → Expr → Prop
  | val  : valid_judgment e t
    → is_value e
    → is_candidate_for_ty e t
  | step : valid_judgment e t
    → (∀ e', is_eval_once e e' → is_candidate_for_ty e' t)
    → is_candidate_for_ty e t

namespace is_candidate_for_ty

lemma all_sn (h_candidate : is_candidate_for_ty e t) : sn e := by
  induction h_candidate
  exact is_value_sn (by assumption)
  apply sn.intro
  assumption

lemma all_well_typed (h_candidate : is_candidate_for_ty e t) : valid_judgment e t := by
  induction h_candidate
  repeat assumption

lemma preserved (h_candidate : is_candidate_for_ty e t) (h_step : is_eval_once e e') : is_candidate_for_ty e' t := by
  let h_t := h_candidate.all_well_typed
  induction h_candidate
  case val e'' t' h_t h_val =>
    have h := h_val.no_step
    simp_all
  case step e'' t' h_t ih₁ ih₂ =>
    exact ih₁ _ h_step

end is_candidate_for_ty

namespace valid_judgment

lemma all_candidates (h : valid_judgment e t) : is_candidate_for_ty e t := by
  have h_progress := h.progress
  match h_progress with
    | .inl h_stuck =>
      exact is_candidate_for_ty.val h h_stuck
    | .inr ⟨e', h_step⟩ =>
      have h_preservation := h.preservation h_step
      induction h generalizing e'
      repeat contradiction
      apply is_candidate_for_ty.step
      apply valid_judgment.call
      repeat assumption
      intro e'' h_step'
      

end valid_judgment

