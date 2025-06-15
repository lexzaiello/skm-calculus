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

lemma sn_m : sn SKM[(M n e)] → valid_judgment e t → sn t := by
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

lemma sn_imp_n_steps_eval_normal (e : Expr) : sn e → ∃ n e', is_normal_n n e e' := by
  intro h_sn
  match h_eq : e with
    | SKM[(M n₁)] =>
      use 0
      use SKM[(M n₁)]
      apply m_stuck
    | SKM[(K n)] =>
      use 0
      use SKM[(K n)]
      apply k_stuck
    | SKM[(S n)] =>
      use 0
      use SKM[(S n)]
      apply s_stuck
    | SKM[(((K n_k) x) y)] =>
      match h_sn with
        | .hard h =>
          have h := h x (by apply is_eval_once.k)
          have ⟨n, e_norm, h_norm_step⟩ := sn_imp_n_steps_eval_normal _ h
          use n.succ
          use e_norm
          apply is_normal_n.succ
          apply is_eval_once.k
          exact h_norm_step
    | SKM[((((S n) x) y) z)] =>
      rw [← h_eq] at h_sn
      induction h_sn
      case hard e' h_step hh =>
        have h_eval := is_eval_once.s x y z n
        rw [h_eq] at h_step
        rw [h_eq] at hh
        have h_eval_sn := h_step _ h_eval
        cases h_eval_sn
        
        sorry
    | SKM[((M n) e)] =>
      
      sorry
    | SKM[(lhs rhs)] =>
      rw [← h_eq] at h_sn
      induction h_sn
      case hard e' h_step hh =>
        simp_all
        
        sorry

