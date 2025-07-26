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
syntax "t_out"                                                         : skmexprquot
syntax "(" skmexprquot skmexprquot ")"                                 : skmexprquot
syntax ident                                                           : skmexprquot
syntax "#" ident                                                       : skmexprquot
syntax "(" skmexprquot ")"                                             : skmexprquot

syntax " << " skmexprquot " >> "                                       : term
syntax "SKM`[ " skmexprquot " ] "                                      : term

macro_rules
  | `(SKM`[ $e:skmexprquot ]) => `(<< $e >>)

macro_rules
  | `(<< K >>)                           => `(Lean.Expr.const `Expr.k [])
  | `(<< S >>)                           => `(Lean.Expr.const `Expr.s [])
  | `(<< M >>)                           => `(Lean.Expr.const `Expr.m [])
  | `(<< t_out >>)                       => `(Lean.Expr.const `t_out  [])
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

def mk_trans (e₁ e₂ e₃ step₁ step₂ : Lean.Expr) : Lean.Expr :=
  mkApp5
    (.const `beta_eq.trans [])
    e₁
    e₂
    e₃
    step₁
    step₂

def mk_eval (e₀ e₁ proof : Lean.Expr) : Lean.Expr :=
  mkApp3 (.const `beta_eq.eval []) e₀ e₁ proof

-- Closes a goal of the form `beta_eq e₁ e₂` by recursively evaluating the expression
partial def eval_to (e : Lean.Expr) : Option (EvalResult × Lean.Expr) := do
  let do_trans (e₀ e₁ e_proof : Lean.Expr) : Option (EvalResult × Lean.Expr) :=
    let e' := eval_to e₁

    match e' with
      | .some ⟨e', rst_proof⟩ =>
        some ⟨
          e',
          mk_trans e₀ e₁ e' e_proof rst_proof
        ⟩
      | .none =>
        some ⟨
          e₁,
          e_proof
        ⟩

  match e with
    | SKM`[((K x) y)] =>
      let x_proof := mk_eval e x (mkApp2 (.const `is_eval_once.k []) x y)

      do_trans e x x_proof
    | SKM`[(((S x) y) z)] =>
      let e' := SKM`[((x z) (y z))]
      let xyz_proof := mk_eval e e' (mkApp3 (.const `is_eval_once.s []) x y z)

      do_trans e SKM`[((x z) (y z))] xyz_proof
    | SKM`[(M K)] =>
      let e' := SKM`[(M K)]

      some ⟨
        e',
        mk_eval e e' (.const `is_eval_once.m_k [])
      ⟩
    | SKM`[(M M)] =>
      let e' := SKM`[(M M)]

      some ⟨
        e',
        mk_eval e e' (.const `is_eval_once.m_m [])
      ⟩
    | SKM`[(M S)] =>
      let e' := SKM`[(M S)]

      some ⟨
        e',
        mk_eval e e' (.const `is_eval_once.m_s [])
      ⟩
    | SKM`[(M (e₁ e₂))] =>
      let e' := SKM`[(t_out ((M e₁) e₂))]
      let t_proof := mk_eval e e' (mkApp2 (.const `is_eval_once.m_call []) e₁ e₂)

      do_trans e e' t_proof
    | SKM`[(lhs rhs)] =>
      let maybe_lhs := eval_to lhs
      let maybe_rhs := eval_to rhs

      match maybe_lhs with
        -- We advanced one step
        | .some ⟨lhs', proof⟩ =>
          let d_proof := mkApp (.const `beta_eq.rfl []) SKM`[(lhs' rhs)]
          let ⟨final, rst_proof⟩ := (eval_to SKM`[(lhs' rhs)]).getD ⟨SKM`[(lhs' rhs)], d_proof⟩

          let e₁ := SKM`[(lhs rhs)]
          let e₂ := SKM`[(lhs' rhs)]
          let e₃ := final

          some ⟨final, mk_trans
            e₁
            e₂
            e₃
            (mkApp4 (.const `beta_eq.left []) lhs lhs' rhs proof)
            rst_proof
          ⟩
        -- We reached a normal form. Try rhs
        | .none =>
          let ⟨rhs', proof⟩ ← maybe_rhs
          let d_proof := mkApp (.const `beta_eq.rfl []) SKM`[(lhs rhs')]
          let ⟨final, rst_proof⟩ := (eval_to SKM`[(lhs rhs')]).getD ⟨SKM`[(lhs rhs')], d_proof⟩

          let e₁ := SKM`[(lhs rhs)]
          let e₂ := SKM`[(lhs rhs')]
          let e₃ := final

          some ⟨final, mk_trans
            e₁
            e₂
            e₃
            (mkApp4 (.const `beta_eq.right []) rhs rhs' lhs proof)
            rst_proof
          ⟩
    | _ => none

syntax "eval_expr" : tactic

elab_rules : tactic
  | `(tactic| eval_expr) => (do
    let some from_e ← get_goal_from_e | throwError "no goal found"
    let mut some ⟨_, proof⟩ := (eval_to from_e) | throwError "no solution found"

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

