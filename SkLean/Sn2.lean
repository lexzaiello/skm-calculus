import SkLean.Ast2
import Mathlib.Tactic

inductive sn : Expr → Prop
  | hard : (∀ e', is_eval_once e e' → sn e') → sn e

namespace sn

lemma k : sn SKM[K n] := by
  apply sn.hard
  intro e' h_eval
  cases h_eval

lemma s : sn SKM[S n] := by
  apply sn.hard
  intro e' h_eval
  cases h_eval

lemma m : sn SKM[M n] := by
  apply sn.hard
  intro e' h_eval
  cases h_eval

lemma call_k : sn SKM[(((K n) x) y)] ↔ sn x := by
  constructor
  intro h_sn
  match h_sn with
    | .hard h_step =>
      exact h_step x (by apply is_eval_once.k)
  intro h_sn
  apply sn.hard
  intro e' h_eval
  cases h_eval
  exact h_sn

lemma call_s : sn SKM[((((S n) x) y) z)] ↔ sn SKM[((x z) (y z))] := by
  constructor
  intro h_sn
  match h_sn with
    | .hard h_step =>
      exact h_step SKM[((x z) (y z))] (by apply is_eval_once.s)
  intro h_sn
  apply sn.hard
  intro e' h_eval
  cases h_eval
  exact h_sn

lemma preserved : sn e → is_eval_once e e' → sn e' := by
  intro h_sn h_eval
  cases e
  cases h_eval
  cases h_eval
  cases h_eval
  case call c =>
    match h_sn with
      | .hard h_step =>
        exact h_step e' h_eval

lemma imp_n_steps_eval_normal (e : Expr) : valid_judgment e t → sn e → ∃ n e', is_normal_n n e e' := by
  intro h_t h_sn
  induction h_t
  case k n =>
    use 0
    use SKM[(K n)]
    apply is_normal_n.stuck
    intro h
    cases h
    case h.a.intro h =>
      cases h
  case s n =>
    use 0
    use SKM[(S n)]
    apply is_normal_n.stuck
    intro h
    cases h
    case h.a.intro h =>
      cases h
  case m n =>
    use 0
    use SKM[(M n)]
    apply is_normal_n.stuck
    intro h
    cases h
    case h.a.intro h =>
      cases h
  case call_k x t_x y t_y n h_t_x h_t_y ih₁ ih₂ =>
    have ⟨n_x_final, x_final, h_x_final⟩ := ih₁ $ call_k.mp h_sn
    use n_x_final.succ
    use x_final
    apply is_normal_n.succ
    apply is_eval_once.k
    exact h_x_final
  case call_s x y z t_call t_x t_y t_z n h_t_call h_t_x h_t_y h_t_z h_u ih₁ ih₂ ih₃ ih₄ =>
    have ⟨n_x_final, x_final, h_x_final⟩ := ih₁ $ call_s.mp h_sn
    use n_x_final.succ
    use x_final
    apply is_normal_n.succ
    apply is_eval_once.s
    exact h_x_final

end sn

namespace valid_judgment

theorem imp_sn : valid_judgment e t → sn e := by
  intro h_t
  induction h_t
  apply sn.k
  apply sn.s
  apply sn.m
  case call_k x t_x n y h_t_x ih =>
    apply sn.hard
    intro e' h_eval'
    have h_e'_eq : e' = x := by
      cases h_eval'
      rfl
      case left lhs' h =>
        cases h
        case left lhs' h =>
          cases h
    rw [← h_e'_eq] at ih
    exact ih

end valid_judgment
