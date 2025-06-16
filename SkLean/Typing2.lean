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
  | hard    : beta_eq t t'            → has_final_judgment e t' → has_final_judgment e t

namespace has_final_judgment

lemma imp_valid_judgment (e : Expr) : has_final_judgment e t → valid_judgment e t := by
  intro h
  induction h
  case trivial _ _ h =>
    exact h.weakening
  case hard t' t'' e' h_step h_t' ih =>
    apply valid_judgment.step_beta_eq
    exact ih
    apply beta_eq.symm
    exact h_step

lemma imp_m : has_final_judgment e t → has_final_judgment e SKM[((M e.max_universe.succ) e)] := by
  intro h
  induction h
  case trivial e' t' h =>
    apply has_final_judgment.hard
    apply beta_eq.eval
    apply is_eval_once.m
    exact h.weakening
    exact has_final_judgment.trivial h
  case hard t' t'' e' h_eval_step h_t' ih =>
    exact ih

lemma preserved : has_final_judgment e t → is_eval_once e e' → has_final_judgment e' t := by
  intro h_t h_eval
  induction h_t
  case trivial e'' t' h =>
    cases e'
    case m m =>
      match m with
        | .mk n =>
          apply has_final_judgment.trivial at h
          apply has_final_judgment.hard
          apply beta_eq.symm
          apply beta_eq.eval
          apply is_eval_once.m
          use (Expr.m m).max_universe.succ
          apply h.imp_valid_judgment
          apply has_final_judgment.hard
          apply beta_eq.right
          apply beta_eq.eval
          exact h_eval
          apply has_final_judgment.hard
          apply beta_eq.eval
          apply is_eval_once.m
          apply valid_judgment.m
          apply has_final_judgment.trivial
          apply valid_judgment_weak.m
    case k k =>
      match k with
        | .mk n =>
          apply has_final_judgment.trivial at h
          apply has_final_judgment.hard
          apply beta_eq.symm
          apply beta_eq.eval
          apply is_eval_once.m
          use (Expr.k k).max_universe.succ
          apply h.imp_valid_judgment
          apply has_final_judgment.hard
          apply beta_eq.right
          apply beta_eq.eval
          exact h_eval
          apply has_final_judgment.hard
          apply beta_eq.eval
          apply is_eval_once.m
          apply valid_judgment.k
          apply has_final_judgment.trivial
          apply valid_judgment_weak.k
    case s s =>
      match s with
        | .mk n =>
          apply has_final_judgment.trivial at h
          apply has_final_judgment.hard
          apply beta_eq.symm
          apply beta_eq.eval
          apply is_eval_once.m
          use (Expr.s s).max_universe.succ
          apply h.imp_valid_judgment
          apply has_final_judgment.hard
          apply beta_eq.right
          apply beta_eq.eval
          exact h_eval
          apply has_final_judgment.hard
          apply beta_eq.eval
          apply is_eval_once.m
          apply valid_judgment.s
          apply has_final_judgment.trivial
          apply valid_judgment_weak.s
    case call c =>
      match c with
        | .mk lhs rhs =>
          cases h
          cases h_eval
          cases h_eval
          cases h_eval
          case call lhs' rhs' h_u h_t_lhs h_t_rhs =>
            cases h_t_lhs
  case hard t'' t''' e' h_beq h_t' ih =>
    simp_all
    apply has_final_judgment.hard
    exact h_beq
    exact ih

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
    apply has_final_judgment.trivial at h_t_lhs
    apply has_final_judgment.trivial at h_t_lhs
    sorry
  case step_beta_eq t' h_t =>
    
    sorry

theorem preserved : valid_judgment e t → is_eval_once e e' → valid_judgment e' t := by
  intro h_t h_eval
  
  sorry

end valid_judgment
