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

  let some ⟨from_e, _⟩ ← parse_beta_eq_call goal_e | return none

  pure from_e

def EvalResult := Lean.Expr

-- Closes a goal of the form `beta_eq e₁ e₂` by recursively evaluating the expression
partial def eval_to (e : Lean.Expr) : MetaM $ Option (EvalResult × Lean.Expr) := do
  logInfo s!"{e}"
  match (← whnf e) with
    | SKM`[((K x) y)] =>
      pure $ some ⟨
        x,
        ← mkAppM `beta_eq.eval #[mkApp2 (.const `is_eval_once.k []) x y]
      ⟩
    | SKM`[(((S x) y) z)] =>
      pure $ some ⟨
        SKM`[((x z) (y z))],
        ← mkAppM `beta_eq.eval #[mkApp3 (.const `is_eval_once.s []) x y z]
      ⟩
    | SKM`[(M K)] =>
      pure $ some ⟨
        SKM`[(M K)],
        ← mkAppM `beta_eq.eval #[.const `is_eval_once.m_k []]
      ⟩
    | SKM`[(M M)] =>
      pure $ some ⟨
        SKM`[(M M)],
        ← mkAppM `beta_eq.eval #[.const `is_eval_once.m_m []]
      ⟩
    | SKM`[(M S)] =>
      pure $ some ⟨
        SKM`[(M S)],
        ← mkAppM `beta_eq.eval #[.const `is_eval_once.m_s []]
      ⟩
    | SKM`[(M (e₁ e₂))] =>
      match (← (liftMetaM $ getConstInfo `t_out)).value? with
        | Option.some e =>
          pure $ some ⟨
            SKM`[(e ((M e₁) e₂))],
            ← mkAppM `beta_eq.eval #[mkApp2 (.const `is_eval_once.m_call []) e₁ e₂]
          ⟩
        | .none => throwError s!"Couldn't find definition for t_out. This is a bug. Please report."
    | SKM`[(lhs rhs)] =>
      let maybe_lhs ← eval_to lhs
      let maybe_rhs ← eval_to rhs

      match maybe_lhs with
        -- We advanced one step
        | .some ⟨lhs', proof⟩ =>
          let d_proof := mkApp (.const `beta_eq.rfl []) SKM`[(lhs' rhs)]
          let ⟨final, rst_proof⟩ := (← eval_to SKM`[(lhs' rhs)]).getD ⟨SKM`[(lhs' rhs)], d_proof⟩

          let proof' ← instantiateMVars proof
          let rst_proof' ← instantiateMVars rst_proof

          let e₁ := SKM`[(lhs rhs)]
          let e₂ := SKM`[(lhs' rhs)]
          let e₃ := final

          pure $ some ⟨final,
               mkApp5
                 (.const `beta_eq.trans [])
                 e₁
                 e₂
                 e₃
                 (mkApp4 (.const `beta_eq.left []) lhs lhs' rhs proof')
                 rst_proof'⟩
        -- We reached a normal form. Try rhs
        | .none =>
          match maybe_rhs with
            | .some ⟨rhs', proof⟩ =>
              let d_proof := mkApp (.const `beta_eq.rfl []) SKM`[(lhs rhs')]
              let ⟨final, rst_proof⟩ := (← eval_to SKM`[(lhs rhs')]).getD ⟨SKM`[(lhs rhs')], d_proof⟩

              let proof' ← instantiateMVars proof
              let rst_proof' ← instantiateMVars rst_proof

              let e₁ := SKM`[(lhs rhs)]
              let e₂ := SKM`[(lhs rhs')]
              let e₃ := final

              pure $ some ⟨final,
               mkApp5
                 (.const `beta_eq.trans [])
                 e₁
                 e₂
                 e₃
                 (mkApp4 (.const `beta_eq.right []) rhs rhs' lhs proof')
                 rst_proof'⟩
            | .none => pure none
    | _ => pure none

syntax "eval_expr" : tactic

elab_rules : tactic
  | `(tactic| eval_expr) => (do
    let some from_e ← get_goal_from_e | throwError "no goal found"
    let mut some ⟨_, proof⟩ ← liftMetaM (eval_to from_e) | throwError "no solution found"

    logInfo s!"dispatching proof: {proof}"

    let goal     ← getMainGoal
    goal.assign (← whnf proof)
    replaceMainGoal []
  )

/-
let e_stx ← delab e
      let goal   ← getMainGoal
      let goal_e := (← Term.getMVarDecl goal).type
      let goal_e' ← instantiateMVars goal_e

      try
        logInfo s!"{e} at {goal_e'}"
        evalTactic (← `(tactic| apply $e_stx))
      catch err =>
        let err_msg ← err.toMessageData.format
        logInfo s!"step {e} at {goal_e} failed:\n\n{err_msg}"

      let goal   ← getMainGoal
      let goal_e := (← Term.getMVarDecl goal).type
      let some ⟨from_e, to_e⟩ ← parse_beta_eq_call goal_e | continue
      let from_e' ← instantiateMVars from_e
      let to_e' ← instantiateMVars to_e

      if from_e' == to_e' then
        logInfo "bruh"
        evalTactic (← `(tactic| apply beta_eq.rfl))
-/

example : beta_eq SKM[((K K) K)] SKM[K] := by
  eval_expr

example : beta_eq SKM[((((S K) K) K))] SKM[K] := by
  eval_expr

example : beta_eq SKM[(M (((S K) K) K))] SKM[(M K)] := by
  eval_expr
