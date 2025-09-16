import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Checker.TypeDefs
import SkLean.Error

open Ast
open Ast.Expr

namespace Expr

def eval_step : Expr → Option Expr
  | ⟪ K (#_α) (#_β) (#x) (#y) ⟫ => pure x
  | ⟪ S (#_α) (#_β) (#_γ) (#x) (#y) (#z) ⟫ => pure ⟪ (#x) (#z) ((#y) (#z)) ⟫
  | ⟪ M K (#α) (#β) ⟫ => pure ⟪ (#α) → (#β) → (#α) ⟫
  | ⟪ ((#_t_in) → (#t_out)) (#arg) ⟫ => t_out
  | ⟪ (#lhs) (#rhs) ⟫ => do
    ⟪ (#← eval_step lhs) (#rhs) ⟫
  | _ => .none

partial def eval_unsafe (e : Expr) : Option Expr := do
  let e' := (match e with
  | ⟪ K (#_α) (#_β) (#x) (#y) ⟫ => pure x
  | ⟪ S (#_α) (#_β) (#_γ) (#x) (#y) (#z) ⟫ => pure ⟪ (#x) (#z) ((#y) (#z)) ⟫
  | ⟪ M K (#α) (#β) ⟫ => pure ⟪ (#α) → (#β) → (#α) ⟫
  | ⟪ ((#_t_in) → (#t_out)) (#arg) ⟫ => pure ⟪ (#t_out) (#arg) ⟫
  | ⟪ (#lhs) (#rhs) ⟫ =>
    pure ⟪ (#(eval_unsafe lhs).getD lhs) (#(eval_unsafe rhs).getD rhs) ⟫
  | _ => Option.none).getD e

  if e == e' then
    pure e
  else
    eval_unsafe e'

partial def infer_unsafe : Expr → Except (@TypeError Expr) Expr
  | ⟪ K ⟫ => pure mk_k_type
  | ⟪ S ⟫ => pure mk_s_type
  | ⟪ T ⟫ => pure mk_t_type
  | ⟪ Type ⟫ => pure mk_type_type
  | ⟪ Syntax ⟫ => pure mk_type_syntax
  | ⟪ M K ⟫ => pure mk_m_k_type
  | ⟪ M S ⟫ => pure mk_m_s_type
  | ⟪ -> ⟫ => pure mk_arr_type
  | ⟪ (#f) (#arg) ⟫ => do
    let t_lhs ← infer_unsafe f

    match t_lhs with
    | ⟪ (#t_in) → (#t_out) ⟫ => do
      let t_arg ← infer_unsafe arg

      if t_in == t_arg then
        pure $ (eval_unsafe t_out).getD t_out
      else
        .error (.argument_mismatch t_in t_arg ⟪ (#t_in) → (#t_out) ⟫ arg)
    | _  =>
      let _ ← infer_unsafe ⟪ (#t_lhs) (#arg) ⟫
      pure $ (eval_unsafe ⟪ (#t_lhs) (#arg) ⟫).getD ⟪ (#t_lhs) (#arg) ⟫
  | e => .error (.no_type_not_comb e)

end Expr

#eval toString <$> Expr.infer_unsafe ⟪ T Type ⟫
#eval toString <$> Expr.infer_unsafe ⟪ T ((T Type) → (T Type)) ⟫
#eval toString <$> Expr.infer_unsafe ⟪ K (T Type) (T Type) ⟫
#eval toString <$> Expr.infer_unsafe ⟪ K (T Syntax) (T Syntax) Type Type ⟫
#eval toString <$> Expr.infer_unsafe ⟪ ((T Type) → (T Type)) ⟫
#eval toString <$> Expr.infer_unsafe ⟪ K (T Syntax) (T Syntax) Type Type ⟫

/-
We can interpret K (T Type) (T Type) as a proof or ("constructor") of (T (M K))
We can pattern match on the constructor call to interpret α → β → α.

This isn't congruent with the typing rule, however.
Now we have special cases.

Pattern matching idea.

K α β is a proof of α → β → α

K (M K) _ K y : M K
This is fine.

We don't want to special case M K.
But we want some way to interpret it as α → β → α.

Elaboration within a context?

α → β → α is a constructor for Type.

M K α β = α → β?

It can't be turtles all the way down.
We need to type-check →.
This is just comparing syntax, though.

(t_in → t_out) arg type-checks if type of arg = t_in

M K α β = α → β → α

(t_in → t_out) arg = t_out arg

M K : Type → Syntax

M (M K) : Type → Type → Syntax

app is valid as long as t_left arg type-checks.
It can't be turtles all the way down though.

Type-checking (t_in → t_out) arg requires a special rule.

This is not captured by the type system, because then we would type-check → again.

Recall, T e : Type.

So this doesn't really work.

We need a typing rule for →.
We can't apply something to T whatever.

T is like return.
T and → are our primitives.

→ has special rules.


M K α β = α → β → α

M K α = α → (M (M K)) α
M K α β = α → β → α

K : M K

T should be able to work with anything that produces a Type.
e.g., T Syntax : Type,
but 
-/
