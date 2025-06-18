import SkLean.Ast2

/-
# Hierarchied SK Reducibility Candidates

Doing induction on typing judgments to prove preservation is extremely difficult. The typing judgment is mutually inductive with beta-equality. Lean doesn't provide faculties for this task. We can simplify the task by creating a "candidate set" which represents well-founded induction on the typing judgment.

Ideally we can perform induction on our `is_candidate_for` predicate to prove that a judgment is preserved. We can say that membership in the candidate set for a type `t` implies being of the type `t`.
Being of type `t` is necessary, but not sufficient for membesrhip in the candidate set. We need further guarantees from membership in the set to be able to prove typing preservation.

A simple constraint is that all judgments are either weak judgments (with no beta-eq types), or are one-step equivalent types. Proving preservation given these constraints is relatively simple.
However, proving membership of all validly-typed expressions in the set is not straightforward. We can perhaps imagine mutually inductive types where one type facilitates thhe "interior proof," type preservation, and the other facilitates the "externa," membership in the set.

Alternatively, we can imagine the same definition of valid_judgment, but with a relation per-step of beta-equivalent types which permits the induction.
-/

inductive is_candidate_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e'))                 → is_candidate_n 0 e e
  | succ  : is_eval_once e e'
    → e_final.max_universe < e.max_universe
    → is_candidate_n n e' e_final
    → is_candidate_n n.succ e e_final

namespace is_candidate_for

lemma preserved : is_candidate_n n e e_final → is_eval_once e e' → ∃ n, is_candidate_n n e' e_final := by
  intro h_r h_beq
  induction h_r
  case stuck e'' h =>
    sorry
  case succ e₁ e'' e''' n e_final h_eval h_u h_step =>
    cases h_u
    have h_trans := is_eval_once.trans e_final h_beq
    

lemma imp_judgment : is_candidate_for e t → valid_judgment e t := by
  intro h_r
  induction h_r
  case stuck t' h_step h =>
    exact h
  case step e' t' h_beq h_u =>
    
    sorry

end is_candidate_for

