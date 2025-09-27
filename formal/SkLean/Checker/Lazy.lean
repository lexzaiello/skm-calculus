import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Error

open Ast
open Ast.Expr

namespace Expr

def eval_step : Expr → Option Expr
  | ⟪ eval (K (#_α) (#_β) (#x) (#y)) #_evidence ⟫ => pure x
  | ⟪ eval (S (#_α) (#_β) (#_γ) (#x) (#y) (#z)) #_evidence ⟫ => pure ⟪ (#x) (#z) ((#y) (#z)) ⟫
  | ⟪ (#lhs) (#rhs) ⟫ => do
    ⟪ (#← eval_step lhs) (#rhs) ⟫
  | _ => .none

partial def eval_unsafe (e : Expr) : Option Expr := do
  let e' := (match e with
  | ⟪ eval (K (#_α) (#_β) (#x) (#y)) ⟫ => pure x
  | ⟪ eval (S (#_α) (#_β) (#_γ) (#x) (#y) (#z)) ⟫ => pure ⟪ (#x) (#z) ((#y) (#z)) ⟫
  | ⟪ (#lhs) (#rhs) ⟫ =>
    pure ⟪ (#(eval_unsafe lhs).getD lhs) (#(eval_unsafe rhs).getD rhs) ⟫
  | _ => Option.none).getD e

  if e == e' then
    pure e
  else
    eval_unsafe e'

partial def infer_unsafe : Expr → Except (@TypeError Expr) Expr
  | .ident _ => pure ⟪ Syntax ⟫
  | ⟪ Type ⟫ => pure ⟪ Syntax ⟫
  | ⟪ M Syntax ⟫ => pure ⟪ Syntax ⟫
  | ⟪ -> ⟫ => pure ⟪ Syntax ⟫
  | ⟪ T ⟫ => pure ⟪ (M Syntax) → (M Syntax) → Type ⟫
  | ⟪ eval ⟫ => pure ⟪ (M Syntax) → (M Syntax) → (◇ (M Syntax)) ⟫
  | ⟪ (#lhs) (#rhs) ⟫ => do
    let t_lhs ← infer_unsafe lhs
    let t_rhs ← infer_unsafe rhs

    if t_lhs == ⟪ Syntax ⟫ ∧ t_rhs == ⟪ Syntax ⟫ then
      pure ⟪ Syntax ⟫
    else
      
      sorry
  | e => .error $ .no_type_not_comb e

end Expr

#eval toString <$> Expr.infer_unsafe ⟪ (T Type) → (T Type) ⟫

