import SkLean.Ast3

def sn (e : Expr) : Prop := Acc (λ e' e => is_eval_once e e') e

syntax (name := do_stuck) "do_stuck " : tactic

macro_rules
  | `(tactic| do_stuck) =>
    `(tactic| apply Acc.intro; intro e h_step; contradiction)

namespace sn

@[simp]
lemma k : sn SKM[K] := by
  do_stuck

@[simp]
lemma s : sn SKM[S] := by
  do_stuck

@[simp]
lemma m : sn SKM[M] := by
  do_stuck

lemma preserved : sn e → is_eval_once e e' → sn e' := by
  intro h_sn h_eval
  induction h_sn
  case intro x ih₁ ih₂ =>
    exact ih₁ _ h_eval

lemma intro (h : ∀ e', is_eval_once e e' → sn e') : sn e :=
  Acc.intro e h

end sn

lemma is_value_sn (h_v : is_value e) : sn e := by
  cases h_v
  repeat do_stuck

inductive is_candidate_for_ty : Expr → Expr → Prop
  | val : valid_judgment e t
    → is_value e
    → is_candidate_for_ty e t
  | app : is_candidate_for_ty lhs SKM[(t_in ~> t_out)]
    → is_candidate_for_ty rhs t_out
    → (∀ e', is_eval_once SKM[(lhs rhs)] e' → is_candidate_for_ty e' t_out)
    → is_candidate_for_ty SKM[(lhs rhs)] t_out

namespace is_candidate_for_ty

lemma all_sn (h_candidate : is_candidate_for_ty e t) : sn e := by
  induction h_candidate
  exact is_value_sn (by assumption)
  apply sn.intro
  assumption

lemma all_well_typed (h_candidate : is_candidate_for_ty e t) : valid_judgment_hard e t := by
  induction h_candidate
  

end is_candidate_for_ty

namespace valid_judgment



end valid_judgment

