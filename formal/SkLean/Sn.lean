import SkLean.Ast3

inductive sn : Expr → Prop
  | hard : (∀ e', is_eval_once e e' → sn e') → sn e

syntax (name := do_stuck) "do_stuck " : tactic

macro_rules
  | `(tactic| do_stuck) =>
    `(tactic| apply sn.hard; intro e h_step; contradiction)

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
  case hard e ih₁ ih₂ =>
    simp_all

end sn

lemma is_value_sn (h_v : is_value e) : sn e := by
  cases h_v
  repeat do_stuck

inductive is_candidate_for_ty : Expr → Expr → Prop
  | val   : valid_judgment e t
    → is_value e
    → is_candidate_for_ty e t
  | step  : valid_judgment e t
    → is_candidate_for_ty e t
    → is_eval_once e e'
    → is_candidate_for_ty e' t
  | stuck : valid_judgment e t
    → (∀ e', is_eval_once e e' → is_candidate_for_ty e' t)
    → is_candidate_for_ty e t

namespace is_candidate_for_ty

lemma all_sn (h_candidate : is_candidate_for_ty e t) : sn e := by
  induction h_candidate
  exact is_value_sn (by assumption)
  exact sn.preserved (by assumption) (by assumption)
  case stuck e' t' h_t_e ih₁ ih₂ =>
    have h_t'' := h_t_e.progress
    match h_t'' with
      | .inl h_stuck =>
        exact is_value_sn (by assumption)
      | .inr ⟨t, h_step⟩ =>
        apply sn.hard
        simp_all

lemma all_well_typed (h_candidate : is_candidate_for_ty e t) : valid_judgment_hard e t := by
  induction h_candidate
  assumption
  apply valid_judgment.preservation
  

end is_candidate_for_ty

namespace valid_judgment



end valid_judgment

