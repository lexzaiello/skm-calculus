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
  induction e
  case m n =>
    use 0
    use SKM[M n]
    apply is_normal_n.m_stuck
  case k n =>
    use 0
    use SKM[K n]
    apply is_normal_n.k_stuck
  case s n =>
    use 0
    use SKM[S n]
    apply is_normal_n.s_stuck
  case call lhs rhs h₁ h₂ =>
    sorry

end sn
