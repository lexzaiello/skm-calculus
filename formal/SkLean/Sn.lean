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
  | k    : RC SKM[K]     SKM[(M K)]
  | s    : RC SKM[S]     SKM[(M S)]
  | m    : RC SKM[M]     SKM[(M M)]
  | arr₀ : RC SKM[(#~>)] SKM[(M #~>)]

namespace RC

lemma all_well_typed (h_candidate : RC e t) : valid_judgment e t := by
  induction h_candidate
  case base h _ _  =>
    exact h.well_typed
  repeat assumption
  apply valid_judgment.k₀
  apply valid_judgment.s₀
  apply valid_judgment.m₀
  apply valid_judgment.arr

lemma all_sn (h_candidate : RC e t) : sn e := by
  induction h_candidate
  case base h _ _ =>
    cases h
    repeat do_stuck
  assumption
  repeat do_stuck

lemma call (h_rc_lhs : RC lhs t_lhs) (h_t : valid_judgment SKM[(lhs rhs)] t) : RC SKM[(lhs rhs)] t := by
  induction h_rc_lhs
  case base ih₁ ih₂ =>
    exact ih₁ _ _ h_t
  case arr lhs t_in t_out h_t_lhs h_sn_lhs ih₁ ih₂ =>
    cases h_t
    repeat contradiction
    case call lhs h_t_rhs h_t_lhs' =>
      have h := h_t_lhs'.deterministic h_t_lhs
      simp_all
  apply RC.base
  cases h_t
  apply is_typed_comb.k₁
  assumption
  contradiction
  intro arg t' h_t

end RC

namespace valid_judgment

lemma all_candidates (h : valid_judgment e t) : RC e t := by
  induction e generalizing t
  cases h
  exact RC.k
  cases h
  exact RC.s
  cases h
  exact RC.m
  cases h
  apply RC.arr₀
  case call lhs rhs ih₁ ih₂ =>
    have ⟨t_rhs, ⟨h_t_rhs, h_lhs⟩⟩ := h.valid_call
    match h_lhs with
      | .inl h_t_lhs =>
        apply RC.call
        exact ih₁ h_t_lhs
        assumption
      | .inr ⟨t_lhs, h_comb_lhs⟩ =>
        apply RC.call
        exact ih₁ h_comb_lhs.well_typed
        assumption

end valid_judgment

