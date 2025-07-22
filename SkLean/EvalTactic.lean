import Lean
import SkLean.Ast3
import Mathlib.Util.AtomM
import Lean.Expr

open Lean Meta Qq
open PrettyPrinter

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

-- Closes a goal of the form `beta_eq e₁ e₂` by recursively evaluating the expression
partial def eval_to (from_e : Lean.Expr) (to_e : Option Lean.Expr) : OptionT MetaM $ List Lean.Expr := do
  if (← (to_e.map $ isDefEq from_e).getD (pure false)) then
    pure [(Lean.Expr.const `beta_eq.rfl []),]
  else match (← whnf from_e) with
    | SKM`[((K x) _y)] =>
      pure $ ([
        (Lean.Expr.const `beta_eq.trans []),
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.k []),
      ]) ++ (← eval_to x to_e)
    | SKM`[(((S x) y) z)] =>
      pure $ ([
        (Lean.Expr.const `beta_eq.trans []),
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.s []),
      ]) ++ (← eval_to SKM`[((x z) (y z))] to_e)
    | SKM`[(M K)] =>
      let e' ← OptionT.mk (pure $ (← getConstInfo `t_k).value?)

      pure $ ([
        (Lean.Expr.const `beta_eq.trans []),
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.m_k []),
      ]) ++ (← eval_to e' to_e)
    | SKM`[(M M)] =>
      let e' ← OptionT.mk (pure $ (← getConstInfo `t_m).value?)

      pure $ ([
        (Lean.Expr.const `beta_eq.trans []),
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.m_m []),
      ]) ++ (← eval_to e' to_e)
    | SKM`[(M S)] =>
      let e' ← OptionT.mk (pure $ (← getConstInfo `t_s).value?)

      pure $ ([
        (Lean.Expr.const `beta_eq.trans []),
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.m_s []),
      ]) ++ (← eval_to e' to_e)
    | SKM`[(M (e₁ e₂))] =>
      let t_out ← OptionT.mk (pure $ (← getConstInfo `t_out).value?)
      let e' := SKM`[(t_out ((M e₁) e₂))]

      pure $ [
        (Lean.Expr.const `beta_eq.trans []),
        (Lean.Expr.const `beta_eq.eval []),
        (Lean.Expr.const `is_eval_once.m_call [])
      ] ++ (← eval_to e' to_e)
    | SKM`[(lhs rhs)] =>
      pure $ [
        (Lean.Expr.const `beta_eq.trans []),
        (Lean.Expr.const `beta_eq.left [])]
          ++ (← eval_to lhs none)
          ++ [
            (Lean.Expr.const `beta_eq.trans []),
            (Lean.Expr.const `beta_eq.right [])]
          ++ (← eval_to rhs none)
    | SKM`[K] => pure [Lean.Expr.const `beta_eq.rfl []]
    | SKM`[S] => pure [Lean.Expr.const `beta_eq.rfl []]
    | SKM`[M] => pure [Lean.Expr.const `beta_eq.rfl []]
    | _ => pure []

def parse_beta_eq_call (e : Lean.Expr) : OptionT MetaM $ Lean.Expr × Lean.Expr := do
  let e ← whnf e
  match e with
    | .app (.app (.const `beta_eq []) from_e) to_e =>
      pure $ ⟨from_e, to_e⟩
    | _ =>
      OptionT.mk (pure .none)

syntax "eval_to" ( term ) : tactic

open Elab Tactic
elab_rules : tactic
  | `(tactic| eval_to $e) => do
    let e' ← (((do
    let goal      ← getMainGoal
    let goal_e := (← Term.getMVarDecl goal).type
    let ⟨from_e, _⟩ ← OptionT.mk (pure $ ← liftMetaM $ parse_beta_eq_call goal_e)
    let to_e ← elabTerm e none

    let exprs ← liftMetaM $ eval_to from_e to_e

    match exprs with
      | Option.some exprs =>
        for e in exprs do
          logInfo s!"{e}"
          let e_stx ← delab e
          evalTactic (← `(tactic| apply $e_stx))
      | .none =>
        return ()) : OptionT TacticM Unit)
          |> OptionT.run)
    pure $ e'.getD ()

example : beta_eq SKM[((K x) y)] x := by
  eval_to x

example : beta_eq SKM[((K (K K)) K)] SKM[(K K)] := by
  eval_to SKM[(K K)]

example : beta_eq SKM[(((S K) K) K)] SKM[K] := by
  eval_to SKM[K]

example : beta_eq SKM[(M ((K K) K))] SKM[(t_out ((M (K K)) K))] := by
  eval_to SKM[(t_out ((M (K K)) K))]

