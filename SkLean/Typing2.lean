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

end valid_judgment_weak

inductive has_final_judgment : Expr → Expr → Prop
  | trivial : valid_judgment_weak e t → has_final_judgment e t
  | hard    : is_eval_once t t'       → has_final_judgment e t' → has_final_judgment e t

namespace has_final_judgment

lemma preserved : has_final_judgment e t → is_eval_once e e' → has_final_judgment e' t := by
  intro h_t h_eval
  induction h_t
  case trivial e'' t' h =>
    apply valid_judgment_weak.eval_preserves_judgment_hard at h
    apply has_final_judgment.trivial
    exact h h_eval
  case hard t'' t''' e'' h_eval' h_final h_step =>
    simp_all
    apply has_final_judgment.hard
    exact h_eval'
    exact h_step

lemma imp_valid_judgment : has_final_judgment e t → valid_judgment e t := by
  intro h
  induction h
  case trivial h =>
    apply valid_judgment_weak.weakening
    exact h
  case hard t'' t''' e' h_t_eq h_t h_t'' =>
    apply valid_judgment.step_beta_eq
    exact h_t''
    exact h_t_eq

lemma imp_exists_valid_judgment_weak : has_final_judgment e t → ∃ t, valid_judgment_weak e t := by
  intro h
  induction h
  case trivial e' t' h =>
    use t'
  case hard t' t'' e' h_eval h_t' ih =>
    exact ih

end has_final_judgment

namespace valid_judgment

lemma imp_has_final_judgment : valid_judgment e t → has_final_judgment e t := by
  intro h
  cases h
  case k =>
    apply has_final_judgment.trivial
    apply valid_judgment_weak.k
  case s =>
    apply has_final_judgment.trivial
    apply valid_judgment_weak.s
  case m =>
    apply has_final_judgment.trivial
    apply valid_judgment_weak.m
  case call lhs rhs h_u h_t_lhs h_t_rhs =>
    apply has_final_judgment.hard
    
    exact h_u
    
    sorry
  case step_beta_eq t' h_t
  sorry

theorem preserved : valid_judgment e t → is_eval_once e e' → valid_judgment e' t := by
  intro h_t h_eval
  
  sorry

end valid_judgment
