import SkLean.Ast3

def sn : Expr → Prop := Acc (λ e' e => is_eval_once e e')

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

inductive RC : Expr → Expr → Prop
  | base : is_typed_comb e t
    → (∀ arg t', valid_judgment SKM[(e arg)] t' → RC SKM[(e arg)] t')
    → RC e t
  | arr  : valid_judgment lhs SKM[(t_in ~> t_out)]
    → sn lhs
    → (∀ arg, valid_judgment arg t_in → RC SKM[(lhs arg)] t_out)
    → RC lhs SKM[(t_in ~> t_out)]
  | val  : is_value e
    → valid_judgment e t
    → RC e t

namespace is_candidate_for_ty

lemma all_well_typed (h_candidate : RC e t) : valid_judgment e t := by
  induction h_candidate
  case base h _ _  =>
    exact h.well_typed
  repeat assumption

lemma all_sn (h_candidate : RC e t) : sn e := by
  induction h_candidate
  case base h _ _ =>
    cases h
    repeat do_stuck
  assumption
  exact is_value_sn (by assumption)

lemma call (h_rc_lhs : RC lhs t_lhs) (h_rc_rhs : RC rhs t_rhs) (h_t : valid_judgment SKM[(lhs rhs)] t) : RC SKM[(lhs rhs)] t := by
  induction h_rc_lhs
  case base ih₁ ih₂ =>
    exact ih₁ _ _ h_t
  case arr lhs t_in t_out h_t_lhs h_sn_lhs ih₁ ih₂ =>
    cases h_t
    repeat contradiction
    case call lhs h_t_rhs h_t_lhs =>
      
      sorry

end is_candidate_for_ty

namespace valid_judgment

lemma all_candidates (h : valid_judgment e t) : is_candidate_for_ty e t := by
  induction e generalizing t
  cases h
  constructor
  apply valid_judgment.k₀
  do_stuck
  unfold is_candidate_for_ty
  cases h
  simp
  apply valid_judgment.s₀
  unfold is_candidate_for_ty
  cases h
  simp
  apply valid_judgment.m₀
  cases h
  unfold is_candidate_for_ty
  constructor
  apply valid_judgment.arr
  do_stuck
  case call lhs rhs ih₁ ih₂ =>
    have ⟨t_rhs, ⟨h_t_rhs, h_lhs⟩⟩ := h.valid_call
    match h_lhs with
      | .inl h_t_lhs =>
        have h := ih₁ h_t_lhs
        have h₂ := ih₂ h_t_rhs
        apply is_candidate_for_ty.call
        repeat assumption
      | .inr h_comb_lhs =>
        
        sorry

end valid_judgment

