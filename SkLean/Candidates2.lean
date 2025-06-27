import SkLean.Ast2
import SkLean.Sn2

inductive is_candidate_for_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e'))
    → valid_judgment e t
    → is_candidate_for_n 0 e t
  | step  : is_eval_once e e'
    → is_candidate_for_n n e' t'
    → e.valid_universes
    → is_candidate_for_n n.succ e t

namespace valid_judgment

lemma imp_valid_universes : valid_judgment e t → e.valid_universes := by
  intro h
  induction h
  apply Expr.valid_universes.k
  apply Expr.valid_universes.s
  apply Expr.valid_universes.m
  apply Expr.valid_universes.call
  case call.a lhs rhs h_u h_t_lhs h_t_rhs h_u_lhs h_u_rhs =>
    exact h_u
  case call.a lhs rhs h_u h_t_lhs h_t_rhs h_u_lhs h_u_rhs =>
    exact h_u_lhs
  case call.a lhs rhs h_u h_t_lhs h_t_rhs h_u_lhs h_u_rhs =>
    exact h_u_rhs

end valid_judgment

namespace is_candidate_for_n

lemma imp_valid_universes : is_candidate_for_n n e t → e.valid_universes := by
  intro h
  induction h
  case stuck e' t' h_stuck h_t =>
    apply h_t.imp_valid_universes
  case step e e' t' t'' h_eval h_candidate h_u _ =>
    exact h_u

end is_candidate_for_n

namespace valid_judgment

lemma imp_well_typed_lhs_rhs : valid_judgment SKM[(lhs rhs)] SKM[((M SKM[(lhs rhs)].max_universe.succ) (lhs rhs))] → valid_judgment lhs SKM[((M lhs.max_universe.succ) lhs)] ∧ valid_judgment rhs SKM[((M rhs.max_universe.succ) rhs)] := by
  intro h_t
  cases h_t
  simp_all

lemma imp_is_candidate_for : valid_judgment e t → ∃ n, is_candidate_for_n n e t := by
  intro h_t
  induction h_t
  use 0
  apply is_candidate_for_n.stuck
  intro h
  obtain ⟨e', h⟩ := h
  cases h
  apply valid_judgment.k
  use 0
  apply is_candidate_for_n.stuck
  intro h
  obtain ⟨e', h⟩ := h
  cases h
  apply valid_judgment.s
  use 0
  apply is_candidate_for_n.stuck
  intro h
  obtain ⟨e', h⟩ := h
  cases h
  apply valid_judgment.m
  case call lhs rhs h_u h_t_lhs h_t_rhs h_candidate_lhs h_candidate_rhs =>
    if h_eval : ∃ e', is_eval_once SKM[(lhs rhs)] e' then
      obtain ⟨e', h_eval⟩ := h_eval
      apply @is_candidate_for_n.step _ e'
      exact h_eval
      
      sorry
    else
      apply is_candidate_for.stuck
      exact h_eval

end valid_judgment

namespace is_candidate_for

lemma imp_sn : is_candidate_for_n e t → sn e := fun ⟨_, h_t_lhs, h_t_rhs⟩ => by
  induction h_t_lhs
  apply sn.k
  apply sn.s
  apply sn.m
  case call lhs rhs h_u h_t_lhs h_t_rhs h_candidate_lhs h_candidate_rhs ih =>
    cases h_t_rhs
    simp_all
    apply valid_judgment.imp_is_candidate_for at h_t_lhs
    apply valid_judgment.imp_is_candidate_for at h_t_rhs
    simp_all
    match h : SKM[(lhs rhs)] with
      | SKM[(((K n) x) y)] =>
        simp_all
        apply sn.hard
        intro e' h
        cases h
        cases h_t_lhs
        case a.k.intro a b c h_left e =>
          cases h_left
      | SKM[((((S n) x) y) z)] =>
        simp_all
        cases h_t_lhs
        case intro h_left _ =>
          cases h_left
      | SKM[((M n) e)] =>
        simp_all
        apply sn.hard
        intro e' h_eval
        induction e
        cases h_eval
        apply sn.m
        cases h_eval
        apply sn.k
        cases h_eval
        apply sn.s
        case a.call a b c d e f g =>
          induction ih
          sorry
      | SKM[(lhs rhs)] =>
        simp_all
        cases h_t_lhs
        case intro h_left _ =>
          cases h_left
          
      | SKM[S rhs] =>
        simp_all
      | SKM[K rhs] =>
        simp_all
      | SKM[M rhs] =>
        simp_all

lemma imp_judgment : is_candidate_for e t → valid_judgment e t :=
  fun ⟨h_t_lh, _⟩ => h_t_lh

lemma imp_valid_universes : is_candidate_for e t → e.valid_universes :=
  fun ⟨_, h_t_rh⟩ => h_t_rh

end is_candidate_for

namespace valid_judgment

theorem imp_sn : valid_judgment e t → sn e := by
  intro h_t
  apply is_candidate_for.imp_sn
  apply imp_is_candidate_for
  exact h_t

lemma imp_sn_weak : valid_judgment e t → beta_eq t t' → sn e := by
  sorry

end valid_judgment
