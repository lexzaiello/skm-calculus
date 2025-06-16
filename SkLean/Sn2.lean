import SkLean.Ast2
import Mathlib.Tactic

inductive sn : Expr → Prop
  | hard : (∀ e', is_eval_once e e' → sn e') → sn e

lemma sn_call_k : sn SKM[(((K n) x) y)] → sn x := by
  intro h_sn
  match h_sn with
    | .hard h_step =>
      exact h_step x (by apply is_eval_once.k)

lemma sn_call_s : sn SKM[((((S n) x) y) z)] → sn SKM[((x z) (y z))] := by
  intro h_sn
  match h_sn with
    | .hard h_step =>
      exact h_step SKM[((x z) (y z))] (by apply is_eval_once.s)

lemma sn_call_m : sn SKM[(M n e)] → valid_judgment e t → sn t := by
  intro h_sn h_t
  match h_sn with
    | .hard h_step =>
      exact h_step t (by apply is_eval_once.m; exact h_t)

lemma sn_preserved : sn e → is_eval_once e e' → sn e' := by
  intro h_sn h_eval
  cases e
  cases h_eval
  cases h_eval
  cases h_eval
  case call c =>
    match h_sn with
      | .hard h_step =>
        exact h_step e' h_eval

lemma sn_imp_n_steps_eval_normal (e : Expr) : valid_judgment e t → sn e → ∃ n e', is_normal_n n e e' := by
  intro h_t h_sn
  induction h_sn
  case hard e' h_step h_eval' =>
    match e' with
      | SKM[M n] =>
        use 0
        use SKM[M n]
        apply m_stuck
      | SKM[K n] =>
        use 0
        use SKM[K n]
        apply k_stuck
      | SKM[S n] =>
        use 0
        use SKM[S n]
        apply s_stuck
      | SKM[(((K n) x) y)] =>
        have h_x_sn := h_step x (by apply is_eval_once.k)
        have ⟨n_norm, norm_x, h_norm_x⟩ := h_eval' x (by apply is_eval_once.k) (by sorry)
        use n_norm.succ
        use norm_x
        apply is_normal_n.succ
        apply is_eval_once.k
        exact h_norm_x
      | SKM[((((S n) x) y) z)] =>
        have h_eval_sn := h_step SKM[((x z) (y z))] (by apply is_eval_once.s)
        have ⟨n_norm, norm_eval, h_norm_eval⟩ := h_eval' SKM[((x z) (y z))] (by apply is_eval_once.s) sorry
        use n_norm.succ
        use norm_eval
        apply is_normal_n.succ
        apply is_eval_once.s
        exact h_norm_eval
      | SKM[(M n e)] =>
        have h_eval_sn := h_step t (by apply is_eval_once.m)
        have ⟨n_norm, norm_eval, h_norm_eval⟩ := h_eval' SKM[((x z) (y z))] (by apply is_eval_once.s) sorry
        use n_norm.succ
        use norm_eval
        apply is_normal_n.succ
        apply is_eval_once.s
        exact h_norm_eval
        sorry
      | SKM[(lhs rhs)] => sorry

