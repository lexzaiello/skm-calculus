import Mathlib.Tactic
import SkLean.DependentExamples

theorem progress : valid_judgment e t → ∃ e', is_eval_once e e' := by
  intro h_t
  cases h_t
  case k n =>
    use SKM[K n]
    apply is_eval_once.k_rfl
  case s n =>
    use SKM[S n]
    apply is_eval_once.s_rfl
  case m n =>
    use SKM[M n]
    apply is_eval_once.m_rfl
  case call lhs rhs h_u h_t_lhs h_t_rhs =>
    match h : SKM[(lhs rhs)] with
      | SKM[(((K n) x) y)] =>
        use x
        apply is_eval_once.k
      | SKM[(((S n x) y) z)] =>
        use SKM[((x z) (y z))]
        apply is_eval_once.s
      | SKM[(M n e)] =>
        use (.call (.mk (.m (.mk lhs.max_universe.succ)) lhs))
        apply is_eval_once.m
        simp_all
        have h_t_lhs' := valid_judgment.step_beta_eq _ _ _ h_t_lhs (by
          apply is_eval_once.m
          apply valid_judgment.m
        )
        simp [Expr.max_universe] at *
        apply valid_judgment.step_beta_eq
        exact h_t_rhs
        
      | SKM[(lhs rhs)] =>
        sorry
      | _ => sorry
  case step_beta_eq t' h_t' h_step =>
    sorry

namespace valid_judgment

theorem beta_eq : valid_judgment e t₁ → beta_eq t₁ t₂ → valid_judgment e t₂ := by
  intro h_t h_beq
  cases h_beq
  case rfl =>
    exact h_t
  case eval h =>
    apply valid_judgment.step_beta_eq
    exact h_t
    exact h
  case left lhs lhs' rhs h_eq' =>
    cases h_t
    case call lhs₁ rhs₁ h_u₁ h_t_lhs h_t_rhs =>
      have h_t₀ := valid_judgment.call _ _ h_u₁ h_t_lhs h_t_rhs
      
    case step_beta_eq t₁ h_t₁ h_step =>
      sorry
  case right lhs rhs rhs' h_eq' =>
    sorry
  case trans e h_eq₁ h_eq₂ =>
    sorry

end valid_judgment

lemma valid_judgment_imp_valid_universes_hard : valid_judgment e t → e.valid_universes := by
  intro h_t
  cases h_t
  apply Expr.valid_universes.k
  apply Expr.valid_universes.s
  apply Expr.valid_universes.m
  case call lhs rhs h_u h_t_lhs h_t_rhs =>
    apply Expr.valid_universes.call
    exact h_u
    apply valid_judgment_imp_valid_universes_hard at h_t_lhs
    exact h_t_lhs
    apply valid_judgment_imp_valid_universes_hard at h_t_rhs
    exact h_t_rhs
  case beta_eq t' h_t_t' h_beta_eq_t' =>
    cases h_t_t'
    apply Expr.valid_universes.k
    apply Expr.valid_universes.s
    apply Expr.valid_universes.m
    apply Expr.valid_universes.call
    case call.a _ _ h_u _ _ =>
      exact h_u
    case call.a lhs rhs h_u h_t_lhs h_t_rhs =>
      apply valid_judgment_imp_valid_universes_hard
      exact h_t_lhs
    case call.a lhs rhs h_u h_t_lhs h_t_rhs =>
      apply valid_judgment_imp_valid_universes_hard
      exact h_t_rhs
    case beta_eq t_step h_t h_beq =>
      cases h_beta_eq_t'
      case rfl =>
        cases h_beq
        
        sorry

lemma valid_judgment_imp_m : ∀ n, valid_judgment e t → valid_judgment e SKM[((M n) e)] := by
  intro n h
  apply valid_judgment.beta_eq
  exact h
  apply beta_eq.symm
  apply beta_eq.eval
  apply is_eval_once.m
  exact h

lemma eval_preserves_judgment : ∀ e e' t, valid_judgment e t → is_eval_once e e' → valid_judgment e' t' → valid_judgment e' t := by
  intro c e' t h_t h_eval h_t'
  cases h_eval
  case k y n =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m (e'.max_universe.succ)
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
    apply beta_eq.symm
    apply beta_eq.trans
    apply beta_eq.symm
    apply beta_eq.eval
    apply is_eval_once.m
    use 0
    exact h_t
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.right
    apply is_eval_once.k
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
  case s x y z n =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m (SKM[((x z) (y z))].max_universe.succ)
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
    apply beta_eq.symm
    apply beta_eq.trans
    apply beta_eq.symm
    apply beta_eq.eval
    apply is_eval_once.m
    use 0
    exact h_t
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.right
    apply is_eval_once.s
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
  case m e'' n h =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m (e''.max_universe.succ)
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
    apply beta_eq.symm
    apply beta_eq.trans
    apply beta_eq.symm
    apply beta_eq.eval
    apply is_eval_once.m
    use 0
    exact h_t
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.right
    apply is_eval_once.m
    exact h
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
  case left lhs lhs' rhs h_eq =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m
    use 0
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.right
    apply beta_eq.left
    apply beta_eq.symm
    apply beta_eq.eval h_eq
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t
  case right rhs rhs' lhs h_eq =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m
    use 0
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.right
    apply beta_eq.right
    apply beta_eq.symm
    apply beta_eq.eval h_eq
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t
  case k_rfl =>
    exact h_t
  case s_rfl =>
    exact h_t
  case m_rfl =>
    exact h_t

lemma eval_preserves_judgment_hard' : ∀ e e' t, valid_judgment e t → is_eval_once e e' → valid_judgment e' t := by
  intro e e' t h_t h_eval
  cases h_t
  case k n =>
    cases h_eval
    apply valid_judgment.k
  case s =>
    cases h_eval
    apply valid_judgment.s
  case m =>
    cases h_eval
    apply valid_judgment.m
  case call lhs rhs h_u h_t_lhs h_t_rhs  =>
    match h_e'_eq : e' with
      | .m (.mk n) =>
        apply valid_judgment.beta_eq
        apply valid_judgment.m
        apply beta_eq.symm
        have h_eval_beq := beta_eq.eval h_eval
        apply beta_eq.trans
        apply beta_eq.left
        apply beta_eq.eval
        apply is_eval_once.m
        exact h_t_lhs
        apply beta_eq.symm
        apply beta_eq.trans
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m
        use n
        apply valid_judgment.m
        apply beta_eq.trans
        apply beta_eq.right
        exact (beta_eq.symm h_eval_beq)
        apply beta_eq.trans
        apply beta_eq.eval
        apply is_eval_once.m
        apply valid_judgment.call
        exact h_u
        exact h_t_lhs
        exact h_t_rhs
        apply beta_eq.rfl
      | .k (.mk n) =>
        apply valid_judgment.beta_eq
        apply valid_judgment.k
        apply beta_eq.symm
        have h_eval_beq := beta_eq.eval h_eval
        apply beta_eq.trans
        apply beta_eq.left
        apply beta_eq.eval
        apply is_eval_once.m
        exact h_t_lhs
        apply beta_eq.symm
        apply beta_eq.trans
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m
        use n
        apply valid_judgment.k
        apply beta_eq.trans
        apply beta_eq.right
        exact (beta_eq.symm h_eval_beq)
        apply beta_eq.trans
        apply beta_eq.eval
        apply is_eval_once.m
        apply valid_judgment.call
        exact h_u
        exact h_t_lhs
        exact h_t_rhs
        apply beta_eq.rfl
      | .s (.mk n) =>
        apply valid_judgment.beta_eq
        apply valid_judgment.s
        apply beta_eq.symm
        have h_eval_beq := beta_eq.eval h_eval
        apply beta_eq.trans
        apply beta_eq.left
        apply beta_eq.eval
        apply is_eval_once.m
        exact h_t_lhs
        apply beta_eq.symm
        apply beta_eq.trans
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m
        use n
        apply valid_judgment.s
        apply beta_eq.trans
        apply beta_eq.right
        exact (beta_eq.symm h_eval_beq)
        apply beta_eq.trans
        apply beta_eq.eval
        apply is_eval_once.m
        apply valid_judgment.call
        exact h_u
        exact h_t_lhs
        exact h_t_rhs
        apply beta_eq.rfl
      | .call (.mk lhs' rhs') =>
        have h_t_lhs' := eval_preserves_judgment_hard' lhs lhs' _ h_t_lhs
        have h_t_rhs' := eval_preserves_judgment_hard' rhs rhs' _ h_t_rhs
        cases h_eval
        apply valid_judgment.beta_eq
        apply valid_judgment.call
        simp [Expr.max_universe] at *
        
        sorry

lemma congr_m : valid_judgment a t
  → valid_judgment b t
  → beta_eq a b
  → beta_eq (Expr.call (.mk (.m (.mk a.max_universe.succ)) a)) (.call (.mk (.m (.mk b.max_universe.succ)) b)) := by
    intro h_t_lhs h_t_rhs h
    simp [Expr.max_universe]
    cases h_t_lhs
    cases h_t_rhs
    cases h
    apply beta_eq.rfl
    apply beta_eq.rfl
    apply beta_eq.rfl
    apply beta_eq.rfl
    cases h
    apply beta_eq.rfl
    case k.beta_eq.eval rhs h₂ h₃ h₄ h₅ =>
      simp [Expr.max_universe] at *
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      apply valid_judgment.k
      simp
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h₃
      exact h₄
    case k.beta_eq.symm rhs h₂ h₃ h₄ h₅ =>
      simp [Expr.max_universe] at *
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      apply valid_judgment.k
      simp
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h₃
      exact h₄
    case k.beta_eq.trans rhs h_rhs h₂ h₃ h₄ h₅ =>
      apply beta_eq.trans
      apply beta_eq.right
      exact h₄
      apply beta_eq.trans
      apply beta_eq.right
      exact h₅
      simp [Expr.max_universe]
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_rhs
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_rhs
      apply beta_eq.rfl
    case s =>
      apply beta_eq.trans
      apply beta_eq.right
      exact h
      simp [Expr.max_universe]
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_t_rhs
      simp
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_t_rhs
      simp
      exact beta_eq.rfl
    case m =>
      apply beta_eq.trans
      apply beta_eq.right
      exact h
      simp [Expr.max_universe]
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_t_rhs
      simp
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_t_rhs
      simp
      exact beta_eq.rfl
    case call lhs rhs h_u h_t_lhs h_t_rhs =>
      simp [Expr.max_universe] at *
      apply beta_eq.trans
      apply beta_eq.right
      exact h
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_t_rhs
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_t_rhs
      apply beta_eq.rfl
    case beta_eq t' h_t' h_eq =>
      have h_t_lhs'' := valid_judgment.beta_eq _ _ _ h_t' h_eq
      have h_t_rhs'' := valid_judgment.beta_eq _ _ _ h_t_rhs (beta_eq.symm h_eq)
      apply beta_eq.trans
      apply beta_eq.right
      exact h
      apply beta_eq.trans
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_t_rhs''
      apply beta_eq.symm
      apply beta_eq.eval
      apply is_eval_once.m
      exact h_t_rhs''

lemma valid_judgment_call_imp_judgment_lhs_rhs : valid_judgment SKM[(lhs rhs)] t → (∃ t_lhs, valid_judgment lhs t_lhs) ∧ (∃ t_rhs, valid_judgment rhs t_rhs) := by
  intro h_t
  cases h_t
  case call h_t_lhs h_t_rhs h_u =>
    constructor
    use (.call (.mk (.m (.mk lhs.max_universe.succ)) lhs))
    use (.call (.mk (.m (.mk rhs.max_universe.succ)) rhs))
  case beta_eq t₂ h_t₂ h_t_beq =>
    have h_t₃ := valid_judgment.beta_eq _ _ _ h_t₂ h_t_beq
    constructor
    cases h_t₂
    case left.call =>
      use (.call (.mk (.m (.mk lhs.max_universe.succ)) lhs))
    case left.beta_eq =>
      
    sorry

theorem all_well_typed_sn : ∀ e t, valid_judgment e t → sn e := by
  intro e t h_t
  cases h_t
  case k =>
    apply sn.trivial
    apply is_eval_once.k_rfl
  case s =>
    apply sn.trivial
    apply is_eval_once.s_rfl
  case m =>
    apply sn.trivial
    apply is_eval_once.m_rfl
  case call lhs rhs h_u h_t_lhs h_t_rhs =>
    apply all_well_typed_sn_weak
    
  sorry

theorem all_types_decideable : ∀ e t, valid_judgment e t → ∃ e, valid_judgment_weak e t := by
  intro e t h_t
  cases h_t
  case k n =>
    use SKM[K n]
    apply valid_judgment_weak.k
  case s n =>
    use SKM[S n]
    apply valid_judgment_weak.s
  case m n =>
    use SKM[M n]
    apply valid_judgment_weak.m
  case call lhs rhs h_u h_t_lhs h_t_rhs =>
    apply all_types_decideable at h_t_lhs
    apply all_types_decideable at h_t_rhs
    have ⟨lhs', h_t_lhs'⟩ := h_t_lhs
    have ⟨rhs', h_t_rhs'⟩ := h_t_rhs
    use SKM[(lhs' rhs')]
    cases h_t_lhs'
  case beta_eq t' h_t' h_eq =>
    cases e
    case m =>
      sorry
    case k =>
      sorry
    case s =>
      sorry
    case call c =>
      match c with
        | .mk lhs rhs =>
          
          sorry
