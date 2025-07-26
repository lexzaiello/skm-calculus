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

abbrev EvalResult := Lean.Expr

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
partial def eval_to (e : Lean.Expr) (t_out t_k t_s t_m : Lean.Expr) : EvalResult × Lean.Expr :=
  let do_trans (e₀ e₁ e_proof : Lean.Expr) : EvalResult × Lean.Expr :=
    let ⟨e', rst_proof⟩ := eval_to e₁ t_out t_k t_s t_m

    ⟨
      e',
      mk_trans e₀ e₁ e' e_proof rst_proof
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
      let e' := t_k

      ⟨
        e',
        mk_eval e e' (.const `is_eval_once.m_k [])
      ⟩
    | SKM`[(M M)] =>
      let e' := t_m

      ⟨
        e',
        mk_eval e e' (.const `is_eval_once.m_m [])
      ⟩
    | SKM`[(M S)] =>
      let e' := t_s

      ⟨
        e',
        mk_eval e e' (.const `is_eval_once.m_s [])
      ⟩
    | SKM`[(M (e₁ e₂))] =>
      let e' := SKM`[(t_out ((M e₁) e₂))]
      let t_proof := mk_eval e e' (mkApp2 (.const `is_eval_once.m_call []) e₁ e₂)

      do_trans e e' t_proof
    | SKM`[(lhs rhs)] =>
      let ⟨lhs', lhs_proof⟩ := eval_to lhs t_out t_k t_s t_m
      let ⟨rhs', rhs_proof⟩ := eval_to rhs t_out t_k t_s t_m

      if ¬(lhs' == lhs) then
        dbg_trace s!"lhs: {lhs} -> {lhs'} via {lhs_proof}"
        do_trans e SKM`[(lhs' rhs)] (mkApp4 (.const `beta_eq.left []) lhs lhs' rhs lhs_proof)
      else if ¬(rhs' == rhs) then
        dbg_trace s!"rhs: {rhs} -> {rhs'} via {rhs_proof}"
        do_trans e SKM`[(lhs rhs')] (mkApp4 (.const `beta_eq.right []) rhs rhs' lhs rhs_proof)
      else
        dbg_trace s!"rfl: {e}"

        ⟨e, mkApp (.const `beta_eq.rfl []) e⟩
    | e => ⟨e, mkApp (.const `beta_eq.rfl []) e⟩

partial def unfold (e : Lean.Expr) : MetaM Lean.Expr := do
  match ← whnf e with
    | Expr.app lhs rhs =>
      pure $ Expr.app (← unfold lhs) (← unfold rhs)
    | Expr.lam n t b c =>
      pure $ Expr.lam n (← unfold t) (← unfold b) c
    | Expr.letE n t v b c =>
      pure $ Expr.letE n (← unfold t) (← unfold v) (← unfold b) c
    | Expr.mdata md b =>
      pure $ Expr.mdata md (← unfold b)
    | Expr.proj n i b =>
      pure $ Expr.proj n i (← unfold b)
    | e' => pure e'

syntax "eval_expr" : tactic

elab_rules : tactic
  | `(tactic| eval_expr) => (do
    let some from_e ← get_goal_from_e | throwError "no goal found"
    let some t_out_def := (← (getConstInfo `t_out)).value? | throwError "missing t_out"
    let some t_k_def := (← (getConstInfo `t_k)).value? | throwError "missing t_k"
    let some t_s_def := (← (getConstInfo `t_s)).value? | throwError "missing t_s"
    let some t_m_def := (← (getConstInfo `t_m)).value? | throwError "missing t_m"
    let t_out ← unfold t_out_def
    let mut ⟨_, proof⟩ := (eval_to (← unfold from_e) t_out (← unfold t_k_def) (← unfold t_s_def) (← unfold t_m_def))

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

example : beta_eq SKM[(t_out ((arrow (M K)) (M S)))] SKM[(M S)] := by
  eval_expr

example : beta_eq SKM[((K K) K)] SKM[K] := by
  eval_expr

example : beta_eq SKM[((((S K) K) K))] SKM[K] := by
  eval_expr
