import SkLean.Ast3

def sn (e : Expr) := Acc (λ e' e => is_eval_once e e') e

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
  case intro e ih₁ ih₂ =>
    exact ih₁ _ h_eval

end sn

lemma is_value_sn (h_v : is_value e) : sn e := by
  cases h_v
  repeat do_stuck

inductive is_candidate_for_ty : Expr → Expr → Prop
  | val : valid_judgment e t
    → is_value e
    → is_candidate_for_ty e t
  | app : is_candidate_for_ty lhs SKM[(t_in ~> t_out)]
    → is_candidate_for_ty rhs t_in
    → is_eval_once SKM[(lhs rhs)] e'
    → is_candidate_for_ty e' t_out
    → is_candidate_for_ty SKM[(lhs rhs)] t_out

namespace is_candidate_for_ty

lemma all_well_typed (h : is_candidate_for_ty e t) : valid_judgment e t := by
  induction h
  repeat assumption
  apply valid_judgment.call
  repeat assumption

lemma all_sn (h_candidate : is_candidate_for_ty e t) : sn e := by
  induction h_candidate
  case val h =>
    exact is_value_sn (by assumption)
  case app lhs t_in t_out rhs e' h_t_lhs h_t_rhs h_step ih₁ ih₂ ih₃ =>
    apply Acc.intro
    intro e' h_step'
    have h_eq : e' = rhs := by
      apply is_eval_once.deterministic
      assumption
      assumption
    rw [← h_eq] at ih₃
    exact ih₃

lemma valid_call (h_candidate_lhs : is_candidate_for_ty lhs SKM[(t_in ~> t_out)]) (h_candidate_rhs : is_candidate_for_ty rhs t_in) : is_candidate_for_ty SKM[(lhs rhs)] t_out := by
  cases h_candidate_lhs
  apply is_candidate_for_ty.stuck
  apply valid_judgment.call
  assumption
  exact h_candidate_rhs.all_well_typed
  intro e' h_step
  have h_t : valid_judgment SKM[(lhs rhs)] t_out := by
    sorry
  have h_t' := h_t.preservation h_step
  apply is_candidate_for_ty.step
  exact h_t'
  
  sorry

end is_candidate_for_ty

namespace valid_judgment

lemma all_candidates (h_t : valid_judgment e t) : is_candidate_for_ty e t := by
  induction h_t
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  case call lhs t_in t_out rhs h_t_lhs h_t_rh sih₁ ih₂ =>
    
    sorry

end valid_judgment

namespace valid_judgment

theorem sn (h_t : valid_judgment e t) : sn e := by
  let h_t₀ := h_t
  induction h_t
  repeat do_stuck
  case call lhs t_in t_out rhs h_t_lhs h_t_rhs ih₁ ih₂ =>
    let e' := h_t₀.progress
    
    sorry

end valid_judgment

