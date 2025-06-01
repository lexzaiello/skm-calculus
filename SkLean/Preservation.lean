/-
# Preservation of SN and Typing Judgements

In order to prove inclusion of all well-typed expressions in our reducibility candidate set, we must first prove:

- That typing judgements are preserved after one-step evaluation
- That membership in the candidate set is preserved after evaluation
-/

import SkLean.Ast
import SkLean.Dsl
import SkLean.Typing
import Mathlib.Tactic

/-
## Preservation of typing judgements

For unevaluable expressions, the judgement is trivially held. I define convenience lemmas for extracing the type ∀ for the left hand side of a function call and the type of the rhs.
-/

lemma match_judgement_call (ctx : Ctx) : ∀ (call : Call) (t : SkExpr), valid_judgement ctx (.call call) t → ∃ bind_ty t_body_old, valid_judgement ctx call.lhs (.fall (.mk bind_ty t_body_old)) ∧ valid_judgement ctx call.rhs bind_ty := by
  intro c t h_judgement_t
  cases h_judgement_t
  case call t_lhs h_t_lhs h_t_rhs h_t =>
    match h : t_lhs with
      | .mk bind_ty ty_body_old =>
        use bind_ty
        use ty_body_old
        simp_all
        unfold Fall.bind_ty at h_t_rhs
        simp at h_t_rhs
        exact h_t_rhs
  case beta_eq t₂ h_judgement_t₂ h_beta_eq =>
    

lemma judgement_holds_eval_once (ctx : Ctx) : ∀ (e : Call) (t : SkExpr), valid_judgement ctx (.call call) t ↔ valid_judgement ctx call.eval_once t := by
  intro c t
  constructor
  intro h
  
  sorry

lemma eval_once_candidate_iff (ctx : Ctx) : ∀ (call : Call) (t : SkExpr), is_candidate_for_t ctx (.call call) t ↔ is_candidate_for_t ctx (call.eval_once) t := by
  intro e t
  constructor
  case mp =>
    intro h
    match h with
      | .fn e' t' t_judgement arg h_t_arg h_redux => sorry
      | .ty e' t' ht' =>
        have h_judgement_t := candidate_for_t_imp_judgement_t ctx (.call e) t h
        -- Since 
        sorry
      | .prp _ _ _ => sorry
      | .fall _ _ _ => sorry
  case mpr =>
    intro h
    sorry
