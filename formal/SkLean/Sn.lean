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

def is_candidate_for_ty : Expr → Expr → Prop
  | e, t@SKM[(t_in ~> t_out)] => valid_judgment e t
    ∧ sn e
    ∧ (∀ arg, is_candidate_for_ty arg t_in → is_candidate_for_ty SKM[(e arg)] t_out)
  | e, t => match t with
    | SKM[((α₁ ~> (β₁ ~> γ₁)) ~> ((α₂ ~> β₂) ~> (α₃ ~> γ₂)))] =>
      α₁ = α₂ ∧ α₂ = α₃ ∧ β₁ = β₂ ∧ γ₁ = γ₂
      ∧ valid_judgment e t
      ∧ sn e
    | SKM[((α₁ ~> (_β ~> α₂)))] => α₁ = α₂ ∧ valid_judgment e t
      ∧ sn e
    | t => valid_judgment e t ∧ sn e

namespace is_candidate_for_ty

lemma all_well_typed (h_candidate : is_candidate_for_ty e t) : valid_judgment e t := by
  induction t
  repeat (cases h_candidate; assumption)
  case call lhs rhs ih₁ ih₂ =>
    cases lhs
    repeat (cases h_candidate; assumption)
    case call a b =>
      cases a
      repeat (cases h_candidate; assumption)

lemma all_sn (h_candidate : is_candidate_for_ty e t) : sn e := by
  cases t
  repeat (cases h_candidate; assumption)
  case call lhs rhs =>
    cases lhs
    repeat (cases h_candidate; assumption)
    case call l ll =>
      cases l
      repeat (cases h_candidate; assumption)
      cases h_candidate
      case arr.intro left right =>
        have ⟨h, _⟩ := right
        assumption
      cases h_candidate
      case call.intro left right =>
        assumption

lemma call (h_candidate_lhs : is_candidate_for_ty lhs SKM[(t_in ~> t_out)]) (h_candidate_rhs : is_candidate_for_ty rhs t_in) : is_candidate_for_ty SKM[(lhs rhs)] t_out := by
  cases h_candidate_lhs
  case intro ih₁ ih₂ =>
    have ⟨ih₂, ih₃⟩ := ih₂
    have h := ih₃ _ h_candidate_rhs
    assumption

lemma call_comb (h_candidate_lhs : is_candidate_for_ty lhs t_lhs) (h_candidate_rhs : is_candidate_for_ty rhs t_rhs)  (h_comb_lhs : is_typed_comb lhs t_lhs) : ∃ t, is_candidate_for_ty SKM[(lhs rhs)] t := by
  have h_t_rhs := h_candidate_rhs.all_well_typed
  induction h_comb_lhs
  exact ⟨SKM[((M K) rhs)], ⟨valid_judgment.k₁ (by assumption), by do_stuck⟩⟩
  case k₁ α t_α h_t_α =>
    exact ⟨SKM[(α ~> (rhs ~> α))], ⟨valid_judgment.k (by assumption) (by assumption), by constructor; do_stuck; sorry⟩⟩
  sorry

end is_candidate_for_ty

namespace valid_judgment

lemma all_candidates (h : valid_judgment e t) : is_candidate_for_ty e t := by
  induction e generalizing t
  cases h
  unfold is_candidate_for_ty
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
        cases h
        
        sorry

end valid_judgment

