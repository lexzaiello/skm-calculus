import Lean
import SkLean.Ast3
import Mathlib.Util.AtomM
import Lean.Expr

open Lean Meta Qq
open PrettyPrinter

-- Closes a goal of the form `beta_eq e₁ e₂` by recursively evaluating the expression
partial def eval_to (from_e : Lean.Expr) (to_e : Option Lean.Expr) : OptionT MetaM $ List Lean.Expr := do
  if (← (to_e.map $ isDefEq from_e).getD (pure false)) then
    pure []
  else match from_e with
    | (.app (.app (.const `SkLean.Ast3.Expr.k []) x) _y) =>
      pure $ ([
        (Lean.Expr.const `SkLean.Ast3.beta_eq.eval []),
        (Lean.Expr.const `SkLean.Ast3.is_eval_once.k []),
      ]) ++ (← eval_to x to_e)
    | (.app (.app (.app (.const `SkLean.Ast3.Expr.s []) x) y) z) =>
      pure $ ([
        (Lean.Expr.const `SkLean.Ast3.beta_eq.eval []),
        (Lean.Expr.const `SkLean.Ast3.is_eval_once.s []),
      ]) ++ (← eval_to (.app (.app x z) (.app y z))  to_e)
    | (.app (.const `SkLean.Ast3.Expr.m []) (.const `SkLean.Ast3.Expr.k [])) =>
      let e' ← OptionT.mk (pure $ (← getConstInfo `SkLean.Ast3.t_k).value?)

      pure $ ([
        (Lean.Expr.const `SkLean.Ast3.beta_eq.eval []),
        (Lean.Expr.const `SkLean.Ast3.is_eval_once.m_k []),
      ]) ++ (← eval_to e' to_e)
    | (.app (.const `SkLean.Ast3.Expr.m []) (.const `SkLean.Ast3.Expr.m [])) =>
      let e' ← OptionT.mk (pure $ (← getConstInfo `SkLean.Ast3.t_m).value?)

      pure $ ([
        (Lean.Expr.const `SkLean.Ast3.beta_eq.eval []),
        (Lean.Expr.const `SkLean.Ast3.is_eval_once.m_m []),
      ]) ++ (← eval_to e' to_e)
    | (.app (.const `SkLean.Ast3.Expr.m []) (.const `SkLean.Ast3.Expr.s [])) =>
      let e' ← OptionT.mk (pure $ (← getConstInfo `SkLean.Ast3.t_s).value?)

      pure $ ([
        (Lean.Expr.const `SkLean.Ast3.beta_eq.eval []),
        (Lean.Expr.const `SkLean.Ast3.is_eval_once.m_s []),
      ]) ++ (← eval_to e' to_e)
    | (.app (.const `SkLean.Ast3.Expr.m []) (.app (.const `SkLean.Ast3.Expr.m []) (.app (.app (.const `SkLean.Ast3.Expr.call []) e₁) e₂))) =>
      let t_out ← OptionT.mk (pure $ (← getConstInfo `SkLean.Ast3.t_out).value?)
      let e' := (Lean.Expr.app (.app (Lean.Expr.const `SkLean.Ast3.Expr.call []) t_out) (.app (.app (.const `SkLean.Ast3.Expr.m []) e₁) e₂))

      pure $ ([
        (Lean.Expr.const `SkLean.Ast3.beta_eq.eval []),
        (Lean.Expr.const `SkLean.Ast3.is_eval_once.m_call [])
      ]) ++ (← eval_to e' to_e)
    | (.app lhs rhs) =>
      pure $ (Lean.Expr.const `SkLean.Ast3.beta_eq.left []) :: (← eval_to lhs none)
    | _ => pure []

syntax "eval_to" ( term ) : tactic

open Elab Tactic
elab_rules : tactic
  | `(tactic| eval_to $e) => do
    let goal      ← getMainGoal
    let goal_e := (← Term.getMVarDecl goal).type

    let exprs ← liftMetaM (OptionT.run $ eval_to goal_e (← elabTerm e none))

    match exprs with
      | Option.some exprs =>
        for e in exprs do
          let e_stx ← delab e
          evalTactic (← `(tactic| apply $e_stx))
      | .none =>
        return ()


