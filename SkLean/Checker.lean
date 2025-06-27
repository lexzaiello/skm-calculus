import SkLean.Ast2
import SkLean.Typing2
import SkLean.Candidates2

inductive maybe_typed : Expr → Prop
  | none : maybe_typed e
  | some : (∃ t, valid_judgment e t) → maybe_typed e

def type_of (e : Expr) : maybe_typed e :=
  match e with
    | SKM[(M n)] => maybe_typed.some ⟨SKM[(M n.succ)], ⟨
      valid_judgment.m n,
      by
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m_final
        apply valid_judgment.m
      ⟩⟩
    | SKM[(S n)] => maybe_typed.some ⟨SKM[(S n.succ)], ⟨
      valid_judgment.s n,
      by
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m_final
        apply valid_judgment.s
      ⟩⟩
    | SKM[(K n)] => maybe_typed.some ⟨SKM[(K n.succ)], ⟨
      valid_judgment.k n,
      by
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m_final
        apply valid_judgment.k
      ⟩⟩
    | SKM[(lhs rhs)] =>
      if h : lhs.max_universe > rhs.max_universe then
        match type_of lhs with
          | .none => .none
          | .some ⟨t_lhs, h_t_lhs⟩ =>
            match type_of rhs with
              | .none => .none
              | .some ⟨t_rhs, h_t_rhs⟩ =>
                have h : valid_judgment SKM[(lhs rhs)] SKM[(((M lhs.max_universe.succ) lhs) ((M rhs.max_universe.succ) rhs))] := by
                  apply valid_judgment.call
                  exact h
                  
                  sorry
            sorry
      else
        maybe_typed.none
