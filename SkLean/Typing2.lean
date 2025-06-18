import SkLean.Ast2

namespace valid_judgment_weak

lemma eval_preserves_judgment_hard : ∀ e e' t, valid_judgment_weak e t → is_eval_once e e' → valid_judgment_weak e' t := by
  intro e e' t h_t h_eval
  cases h_t
  case k n =>
    cases h_eval
  case s =>
    cases h_eval
  case m =>
    cases h_eval
  case call lhs rhs h_u h_t_lhs h_t_rhs  =>
    match h₀ : h_eval with
      | .k lhs' rhs' n =>
        cases h_t_lhs
      | .s x' y' z' n =>
        cases h_t_lhs
      | .left h_eval' =>
        cases h_t_lhs
      | .m e t n h_t =>
        cases h_t_lhs

lemma weakening : valid_judgment_weak e t → valid_judgment e t := by
  intro h
  cases h
  case k =>
    apply valid_judgment.k
  case s =>
    apply valid_judgment.s
  case m =>
    apply valid_judgment.m
  case call lhs rhs h_u h_t_lhs h_t_rhs =>
    apply valid_judgment.call
    exact h_u
    apply weakening at h_t_lhs
    exact h_t_lhs
    apply weakening at h_t_rhs
    exact h_t_rhs

lemma preserved : valid_judgment_weak e t → is_eval_once e e' → valid_judgment_weak e' t := by
  intro h_t
  sorry

lemma imp_has_final_judgment_beta_eq : valid_judgment e t₁ → beta_eq t₁ t₂ → has_final_judgment e t₂ := by
  intro h_t h_eq
  apply has_final_judgment.hard
  exact (beta_eq.symm h_eq)
  cases h_t
  case a.k =>
    apply has_final_judgment.trivial
    apply valid_judgment_weak.k
  case a.s =>
    apply has_final_judgment.trivial
    apply valid_judgment_weak.s
  case a.m =>
    apply has_final_judgment.trivial
    apply valid_judgment_weak.m
  case a.call lhs rhs h_u h_t_lhs h_t_rhs =>
    apply imp_has_final_judgment_call
    exact h_u
    exact h_t_lhs
    exact h_t_rhs
  sorry
termination_by e

end

theorem preserved : valid_judgment e t → is_eval_once e e' → valid_judgment e' t := by
  intro h_t h_eval
  
  sorry

end valid_judgment
