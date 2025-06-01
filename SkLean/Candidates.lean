/-
# Reducibility Candidates

I extend existing proofs of strong normalization of the STLC and simply-typed SK combinators by utilizing Girard's "reducibility candidates."

I define reducibility candidates as expressions of type \\(t\\) which are [hereditarily terminating](https://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/tait.pdf):

- In the case of unevaluable expressions \\(t\\), the expression is trivially hereditarily terminating and a reducibility candidate for type \\(t\\).
- In the case where \\(t\\) is of the form \\(\forall x:\alpha.\beta\\), an expression of type \\(e\\) is strongly-normalizing if all its one-step reduxes are reducibility candidates for \\(\beta\\). The set of one-step reduxes is defined as all applications of \\(e\ arg\\) where \\(arg\\) is of type \\(\alpha\\).
-/

import SkLean.Ast
import SkLean.Dsl
import SkLean.Typing

inductive is_candidate_for_t : Ctx → SkExpr → SkExpr → Prop
  | ty (e : Ty) (t : Ty)   :
    valid_judgement ctx (.ty e) (.ty t)  → is_candidate_for_t ctx (.ty e) (.ty t)
  | prp (e : Prp) (t : Ty) :
    valid_judgement ctx (.prp e) (.ty t) → is_candidate_for_t ctx (.prp e) (.ty t)
  | fall (e : Fall) (t : SkExpr) :
    valid_judgement ctx (.fall e) t → is_candidate_for_t ctx (.fall e) t
  | fn   (e : SkExpr) (t : Fall) :
    valid_judgement ctx e (.fall t) →
    -- All one-step reduxes are reducibility candidates
    ∀ arg, is_candidate_for_t ctx arg t.bind_ty →
      is_candidate_for_t ctx ((Call.mk e arg).eval_once) t.body →
      is_candidate_for_t ctx e (.fall t)

/-
For simplicity in further proofs, we will prove that reducibility candidates for t are of type t:
-/

lemma candidate_for_t_imp_judgement_t (ctx : Ctx) : ∀ (e : SkExpr) (t : SkExpr), is_candidate_for_t ctx e t → valid_judgement ctx e t := by
  intro e t h
  cases h
  case ty h =>
    exact h
  case prp h =>
    exact h
  case fall h =>
    exact h
  case fn _ h _ =>
    exact h

/-
In the [next chapter](./Preservation.lean.md), I prove preservation of typing judgements, and preservation of membership in the candidate set for type \\(t\\) for \\(e : t\\).
-/
