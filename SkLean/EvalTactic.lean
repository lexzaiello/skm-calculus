import Lean
import SkLean.Ast3
import Mathlib.Util.AtomM
import Lean.Expr

open Lean Meta Qq
open PrettyPrinter
open Elab Tactic

declare_syntax_cat skmexprquot
syntax "K"                                                             : skmexprquot
syntax "S"                                                             : skmexprquot
syntax "M"                                                             : skmexprquot
syntax "(" skmexprquot skmexprquot ")"                                 : skmexprquot
syntax ident                                                           : skmexprquot
syntax "#" term                                                        : skmexprquot
syntax "(" skmexprquot ")"                                             : skmexprquot

syntax " << " skmexprquot " >> "                                      : term
syntax "SKM`[ " skmexprquot " ] "                                      : term

macro_rules
  | `(SKM`[ $e:skmexprquot ]) => `(<< $e >>)

macro_rules
  | `(<< K >>)                           => `(Lean.Expr.const `Expr.k [])
  | `(<< S >>)                           => `(Lean.Expr.const `Expr.s [])
  | `(<< M >>)                           => `(Lean.Expr.const `Expr.m [])
  | `(<< $e:ident >>)                    => `($e)
  | `(<< ($e₁:skmexprquot $e₂:skmexprquot) >>)   => `(Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Expr.call []) << $e₁ >>)
    << $e₂ >>)
  | `(<< ($e:skmexprquot) >>)            => `(<<$e>>)

def parse_beta_eq_call (e : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let e ← whnf e
  match e with
    | .app (.app (.const `beta_eq []) from_e) to_e =>
      pure $ pure ⟨from_e, to_e⟩
    | _ =>
      (pure .none)

def get_goal_target_e  : TacticM (Option Lean.Expr) := do
  let goal   ← getMainGoal
  let goal_e := (← Term.getMVarDecl goal).type

  let some ⟨_, to_e⟩ ← parse_beta_eq_call goal_e | return none

  if to_e.hasMVar then
    pure none
  else
    pure to_e

def get_goal_from_e  : TacticM (Option Lean.Expr) := do
  let goal   ← getMainGoal
  let goal_e := (← Term.getMVarDecl goal).type

  let some ⟨from_e, _⟩ ← parse_beta_eq_call goal_e | return none

  pure from_e

-- Closes a goal of the form `beta_eq e₁ e₂` by recursively evaluating the expression
partial def eval_to (to_e : Option Lean.Expr) : TacticM (Option Unit):= do
  let do_apply : List Lean.Expr → TacticM Unit := fun (exprs) => do
    exprs.forM (fun (e) => do
      let e' ← delab e
      evalTactic (← `(tactic| apply $e'))
    )

  let some from_e := (← get_goal_from_e) | return ()

  let to_e ← (do match ← get_goal_target_e with
    | .some g => do
      let _ ← do_apply [(Lean.Expr.const `beta_eq.trans [])]
      pure $ .some g
    | .none =>
      pure to_e)

  if (← liftMetaM (to_e.mapM $ isDefEq from_e)).getD false then
    do_apply [(Lean.Expr.const `beta_eq.rfl []),]
  else match (← whnf from_e) with
    | SKM`[((K x) _y)] =>
      let _ ← do_apply [
        Lean.Expr.const `beta_eq.eval [],
        Lean.Expr.const `is_eval_once.k [],
      ]
      eval_to to_e
    | SKM`[(((S x) y) z)] =>
      let _ ← do_apply [
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.s []),
      ]
      eval_to to_e
    | SKM`[(M K)] =>
      let _ ← do_apply [
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.m_k []),
      ]
      eval_to to_e
    | SKM`[(M M)] =>
      let _ ← do_apply [
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.m_m []),
      ]
      eval_to to_e
    | SKM`[(M S)] =>
      let _ ← do_apply [
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.m_s []),
      ]
      eval_to to_e
    | SKM`[(M (e₁ e₂))] =>
      let _ ← do_apply [
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.m_call []),
      ]
      eval_to to_e
    | SKM`[K] => do_apply [Lean.Expr.const `beta_eq.rfl []]
    | SKM`[S] => do_apply [Lean.Expr.const `beta_eq.rfl []]
    | SKM`[M] => do_apply [Lean.Expr.const `beta_eq.rfl []]
    | SKM`[(lhs rhs)] =>
      let _ ← do_apply [
        (Lean.Expr.const `beta_eq.left [])]
      let _ ← eval_to lhs
      let _ ← do_apply [
             Lean.Expr.const `beta_eq.right []]
      eval_to none
    | _ => pure $ pure ()

syntax "eval_to" ( term ) : tactic

elab_rules : tactic
  | `(tactic| eval_to $e) => (do
    let to_e ← elabTerm e none

    eval_to to_e).bind (fun o => pure $ o.getD ())

example : beta_eq SKM[((K x) y)] x := by
  eval_to x

example : beta_eq SKM[((K (K K)) K)] SKM[(K K)] := by
  eval_to SKM[(K K)]

example : beta_eq SKM[(((S K) K) K)] SKM[K] := by
  eval_to SKM[K]

example : beta_eq SKM[(M (((S K) K) K))] SKM[(t_out ((M ((S K) K)) K))] := by
  eval_to SKM[(t_out ((M ((S K) K)) K))]

example : beta_eq SKM[(M (((S K) K) K))] SKM[(M K)] := by
  eval_to SKM[(M K)]
  trace_state


