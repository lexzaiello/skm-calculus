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

def RC (e t : Expr) : Prop :=
  valid_judgment e t ∧ sn e ∧ (match e, t with
    | e, SKM[(t_in ~> t_out)] => ∀ arg, RC arg t_in → RC SKM[(e arg)] t_out
    | e, t => is_typed_comb e t)

/-
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
-/


syntax (name := obv_rc) "obv_rc" "assumption"? term : tactic

macro_rules
  | `(tactic| obv_rc $e:term) =>
    `(tactic| constructor; apply $e; (repeat assumption); constructor; do_stuck; rfl)

namespace RC

lemma all_well_typed (h_candidate : RC e t) : valid_judgment e t := by
  unfold RC at h_candidate
  simp_all

lemma all_sn (h_candidate : RC e t) : sn e := by
  unfold RC at h_candidate
  simp_all

lemma call (h_candidate_lhs : RC lhs SKM[(t_in ~> t_out)]) (h_candidate_rhs : RC rhs t_in) : RC SKM[(lhs rhs)] t_out := by
  cases h_candidate_lhs
  simp_all

lemma call_comb (h_candidate_lhs : RC lhs t_lhs) (h_candidate_rhs : RC rhs t_rhs) (h_comb_lhs : is_typed_comb lhs t_lhs) : ∃ t, RC SKM[(lhs rhs)] t := by
  have h_t_lhs := h_comb_lhs.well_typed
  have h_t_rhs := h_candidate_rhs.all_well_typed
  induction h_t_lhs
  exact ⟨SKM[((M K) rhs)], ⟨valid_judgment.k₁ (by assumption), ⟨by do_stuck, is_typed_comb.k₁ (by assumption)⟩⟩⟩
  exact ⟨SKM[((M S) rhs)], ⟨valid_judgment.s₁ (by assumption), ⟨by do_stuck, is_typed_comb.s₁ (by assumption)⟩⟩⟩
  exact ⟨t_rhs, ⟨valid_judgment.call (by assumption), ⟨by do_stuck, is_typed_comb.s₁ (by assumption)⟩⟩⟩

end RC

namespace valid_judgment

lemma all_candidates (h : valid_judgment e t) : RC e t := by
  induction e generalizing t
  cases h
  obv_rc valid_judgment.k₀
  cases h
  obv_rc valid_judgment.s₀
  cases h
  obv_rc valid_judgment.m₀
  cases h
  obv_rc valid_judgment.arr
  case call lhs rhs ih₁ ih₂ =>
    have ⟨t_rhs, ⟨h_t_rhs, h_t_lhs⟩⟩ := h.valid_call
    have h_rc_rhs := ih₂ h_t_rhs
    match h_t_lhs with
      | .inl h_t_lhs =>
        have h_rc_lhs := ih₁ h_t_lhs
        sorry
      | .inr h_comb =>
        
        sorry

theorem sn (h : valid_judgment e t) : sn e := h.all_candidates.all_sn

end valid_judgment

