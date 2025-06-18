import SkLean.Ast2
import SkLean.Typing2
import SkLean.Sn2

def is_candidate_for (e : Expr) (t : Expr) : Prop := valid_judgment e t ∧ e.valid_universes

namespace valid_judgment

lemma imp_is_candidate_for : valid_judgment e t → is_candidate_for e t := by
  intro h_t
  unfold is_candidate_for
  induction h_t
  constructor
  apply valid_judgment.k
  apply Expr.valid_universes.k
  constructor
  apply valid_judgment.s
  apply Expr.valid_universes.s
  constructor
  apply valid_judgment.m
  apply Expr.valid_universes.m
  case call lhs rhs h_u h_t_lhs h_t_rhs ih₁ ih₂ =>
    simp_all
    constructor
    apply valid_judgment.call
    exact h_u
    simp_all
    simp_all
    apply Expr.valid_universes.call
    exact h_u
    simp_all
    simp_all

end valid_judgment

namespace is_candidate_for

lemma imp_sn : is_candidate_for e t → sn e := fun ⟨h_t_lhs, h_t_rhs⟩ => by
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
        cases h_t_lhs
        case intro h_left _ =>
          cases h_left
      | SKM[((((S n) x) y) z)] =>
        simp_all
        cases h_t_lhs
        case intro h_left _ =>
          cases h_left
      | SKM[((M n) e)] =>
        simp_all
        cases h_t_lhs
        case intro h_left _ =>
          cases h_left
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

end valid_judgment
