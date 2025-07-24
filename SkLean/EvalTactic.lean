import Lean
import SkLean.Ast3
import Mathlib.Util.AtomM
import Lean.Expr
import Mathlib.Control.Monad.Writer

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

  logInfo s!"main goal: {goal_e}"

  let some ⟨from_e, _⟩ ← parse_beta_eq_call goal_e | return none

  pure from_e

-- Closes a goal of the form `beta_eq e₁ e₂` by recursively evaluating the expression
partial def eval_to (e : Lean.Expr) : WriterT (List Lean.Expr) MetaM Unit := do
  match (← whnf e) with
    | SKM`[((K x) _y)] =>
      tell [Lean.Expr.const `beta_eq.eval [], Lean.Expr.const `is_eval_once.k []]
      eval_to x
    | SKM`[(((S x) y) z)] =>
      tell [Lean.Expr.const `beta_eq.eval [], Lean.Expr.const `is_eval_once.s []]
      eval_to SKM`[((x z) (y z))]
    | SKM`[(M K)] =>
      tell [Lean.Expr.const `beta_eq.eval [], Lean.Expr.const `is_eval_once.m_k []]
    | SKM`[(M M)] =>
      tell [Lean.Expr.const `beta_eq.eval [], Lean.Expr.const `is_eval_once.m_m []]
    | SKM`[(M S)] =>
      tell [Lean.Expr.const `beta_eq.eval [], Lean.Expr.const `is_eval_once.m_s []]
    | SKM`[(M (e₁ e₂))] =>
      match (← liftMetaM $ getConstInfo `t_out).value? with
        | .some e =>
          tell [
            Lean.Expr.const `beta_eq.eval [],
            Lean.Expr.const `is_eval_once.m_call []
          ]

          eval_to SKM`[(e ((M e₁) e₂))]
        | .none =>
          liftMetaM $ throwError s!"Failed at step: {e}"
    | SKM`[(lhs rhs)] =>
      tell [
        Lean.Expr.const `beta_eq.trans [],
        Lean.Expr.const `beta_eq.left []
      ]
      let _ ← eval_to lhs
      tell [Lean.Expr.const `beta_eq.rfl [],
            Lean.Expr.const `beta_eq.trans [],
            Lean.Expr.const `beta_eq.right []
      ]
      let _ ← eval_to rhs

      tell [Lean.Expr.const `beta_eq.rfl []]
    | _ =>
      tell [Lean.Expr.const `beta_eq.rfl []]

syntax "eval_to" ( term ) : tactic

elab_rules : tactic
  | `(tactic| eval_to $e) => (do
    let to_e ← elabTerm e none

    let ⟨_, exprs⟩ ← liftMetaM (eval_to to_e)

    for e in exprs do
      let e_stx ← delab e
      evalTactic (← `(tactic| apply $e_stx))

    pure ()
  )

example : beta_eq SKM[(M (((S K) K) K))] SKM[(M K)] := by
  eval_to SKM[(M K)]


