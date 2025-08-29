import Lean
import SkLean.Ast3
import SkLean.UnsafeEval
import SkLean.Eval
import SkLean.Checker
open Lean

syntax (name := translate) "translate" term : term

def all_sk (e : Lean.Expr) : Bool :=
  match e with
  | .const `Expr.k []
  | .const `Expr.s []
  | .const `Expr.m []
  | (.app (.const `Expr.ty []) _)
  | .const `Expr.arr []=> true
  | .app lhs rhs =>
    all_sk lhs ∧ all_sk rhs
  | _ => false

structure AppInfo where
  lhs'   : Ast.Expr
  rhs'   : Ast.Expr
  ty_lhs : Ast.Expr
  ty_rhs : Ast.Expr
  ty'    : Ast.Expr

structure ConstInfo where
  ty'    : Ast.Expr
  ty_c   : Ast.Expr
  c'     : Ast.Expr

partial def do_translate (ctx : List Ast.Expr) (e : Lean.Expr) : MetaM Ast.Expr := do
  let abstr_app_vars (ctx : List Ast.Expr) (ty lhs rhs : Lean.Expr) : MetaM AppInfo := do
    let ty'    ← do_translate ctx ty
    let ctx' := (ty' :: ctx)
    let ty_lhs ← do_translate ctx' (← Lean.Meta.inferType lhs)
    let ty_rhs ← do_translate ctx' (← Lean.Meta.inferType rhs)
    let lhs'   ← do_translate ctx' lhs
    let rhs'   ← do_translate ctx' rhs

    pure { lhs' := lhs', rhs' := rhs', ty_lhs := ty_lhs, ty_rhs := ty_rhs, ty' := ty' }

  let abstr_const (ctx : List Ast.Expr) (ty c : Lean.Expr) : MetaM ConstInfo := do
    let ty' ← do_translate ctx ty
    let ctx' := (ty' :: ctx)
    let t_c ← do_translate ctx' (← Lean.Meta.inferType c)
    let c' ← do_translate ctx' c

    pure { ty' := ty', c' := c', ty_c := t_c }

  let or_throw {α : Type} (msg : String) (x : Option α) : MetaM α :=
    match x with
      | .some e => pure e
      | _ => throwError s!"{msg}: {e}"

  if all_sk e then
    Ast.Expr.fromExpr e |> or_throw "unsupported expr; was all SK"
  else
    match e with
    | .lam _ ty (.bvar 0) _ =>
      let ty' ← (do_translate ctx ty)

      pure SKM[(((((S (ty' ~> (ty' ~> ty'))) (ty' ~> ty' ~> ty')) ty') ((K ty') (ty' ~> ty'))) ((K ty') ty'))]
    | .lam _ ty (.app lhs rhs) _ =>
      let { lhs', rhs', ty_lhs, ty_rhs, ty' } ← abstr_app_vars ctx ty lhs rhs

      pure SKM[(((((S ty_lhs) ty_rhs) ty') lhs') rhs')]
    | .forallE _ ty (.bvar 0) _ =>
      let ty' ← do_translate ctx ty

      pure SKM[((((((M S) (ty' ~> (ty' ~> ty'))) (ty' ~> ty')) ty') ((K ty') (ty' ~> ty'))) ((K ty') ty'))]
    | .forallE _ ty (.app lhs rhs) _ =>
      let { lhs', rhs', ty_lhs, ty_rhs, ty' } ← abstr_app_vars ctx ty lhs rhs

      pure SKM[((((((M S) ty_lhs) ty_rhs) ty') lhs') rhs')]
    | .lam _ ty (.bvar n) _ =>
      let ty' ← do_translate ctx ty
      let t_v ← ctx[n]? |> or_throw "missing type in context"

      pure SKM[((K t_v) ty')]
    | .lam _ ty c _ =>
      let { ty', ty_c, c' } ← abstr_const ctx ty c
      pure SKM[(((K ty_c) ty') c')]
    | .forallE _ ty (.bvar n) _ =>
      let ty' ← do_translate ctx ty
      let t_v ← ctx[n]? |> or_throw "missing type in context"

      pure SKM[(((M K) t_v) ty')]
    | .forallE _ ty c _ =>
      let { ty', ty_c, c' } ← abstr_const ctx ty c
      pure SKM[((((M K) ty_c) ty') c')]
    | .sort n =>
      let depth := n.depth
      pure SKM[Ty depth.pred]
    | .app lhs rhs =>
      let lhs' ← do_translate ctx lhs
      let rhs' ← do_translate ctx rhs

      pure SKM[(lhs' rhs')]
    | e => throwError s!"unsupported expr: {e}"

elab "translate" e:term : term => do
  let ⟨e, _⟩ ← (Elab.Term.elabTerm e .none).run
  toExpr <$> do_translate [] e

#eval Expr.eval_unsafe $ translate ((λ (x : Type 1) => x) (Type 0))
#eval translate (λ (x : Type 1) (y : Type 2) => x)

