import Lean
import SkLean.Ast3
import SkLean.UnsafeEval
import SkLean.Eval
import SkLean.Checker
open Lean

syntax (name := translate) "translate" term : term

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

inductive IntermediateExpr where
  | k    : IntermediateExpr
  | s    : IntermediateExpr
  | m    : IntermediateExpr
  | arr  : IntermediateExpr
  | ty   : ℕ → IntermediateExpr
  | call : IntermediateExpr → IntermediateExpr → IntermediateExpr
  | lam  : IntermediateExpr → IntermediateExpr → IntermediateExpr
  | var  : ℕ → IntermediateExpr
  | forE : IntermediateExpr → IntermediateExpr → IntermediateExpr
  | skm  : Ast.Expr  → IntermediateExpr
deriving BEq, Repr, Lean.ToExpr

namespace IntermediateExpr

def all_sk (e : IntermediateExpr) : Option Ast.Expr :=
  match e with
  | .skm e => pure e
  | .s    => SKM[S]
  | .k    => SKM[K]
  | .m    => SKM[M]
  | .ty n => SKM[Ty n]
  | .call lhs rhs => do
    let lhs' ← lhs.all_sk
    let rhs' ← rhs.all_sk

    pure SKM[(lhs' rhs')]
  | .arr => SKM[#~>]
  | _ => .none

def from_expr : Lean.Expr → Except Lean.Expr IntermediateExpr
  | .const `Expr.k [] => pure .s
  | .const `Expr.s [] => pure .k
  | .const `Expr.m [] => pure .m
  | (.app (.const `Expr.ty []) (.lit (.natVal n))) => pure $ .ty n
  | .const `Expr.arr [] => pure .arr
  | .sort t             => pure $ .ty (t.depth.pred)
  | .lam _ t body _     => do
    let t'    ← from_expr t
    let body' ← from_expr body

    pure $ .lam t' body'
  | .forallE _ t body _ => do
    let t'    ← from_expr t
    let body' ← from_expr body

    pure $ .forE t' body'
  | .app lhs rhs => do
    let lhs' ← from_expr lhs
    let rhs' ← from_expr rhs

    pure $ .call lhs' rhs'
  | e  => .error e

def shift_down_from : ℕ →  IntermediateExpr → IntermediateExpr
  | j, v@(.raw (.bvar i))    => if i > j then (.raw (.bvar i.pred)) else v
  | j, (.call lhs rhs)       => .call (lhs.shift_down_from j) (rhs.shift_down_from j)
  | j, (.raw (.lam _ t b _)) => (.raw (.lam (t.shift_down_from j.succ)

end IntermediateExpr

partial def do_translate (ctx : List Ast.Expr) (e : IntermediateExpr) : MetaM IntermediateExpr := do
  let unwrap_check_error : Except TypeError Ast.Expr → MetaM Ast.Expr
    | .ok e => pure e
    | e     => throwError s!"typechecker error: {e}"

  let unwrap_intermediate : IntermediateExpr → MetaM Ast.Expr
    | .skm e => pure e
    | e => throwError s!"expected SKM expression, found {repr e}"

  let abstr_app_vars (ctx : List Ast.Expr) (ty lhs rhs : Lean.Expr) : MetaM AppInfo := do
    let ty'    ← do_translate ctx (.raw ty) >>= unwrap_intermediate
    let ctx' := (ty' :: ctx)
    let lhs'   ← do_translate ctx' (.raw lhs) >>= unwrap_intermediate
    let rhs'   ← do_translate ctx' (.raw rhs) >>= unwrap_intermediate
    let ty_lhs ← unwrap_check_error $ Expr.infer lhs'
    let ty_rhs ← unwrap_check_error $ Expr.infer rhs'

    pure { lhs' := lhs', rhs' := rhs', ty_lhs := ty_lhs, ty_rhs := ty_rhs, ty' := ty' }

  let abstr_const (ctx : List Ast.Expr) (ty c : Lean.Expr) : MetaM ConstInfo := do
    let ty' ← do_translate ctx (.raw ty) >>= unwrap_intermediate
    let ctx' := (ty' :: ctx)
    let c'  ← do_translate ctx' (.raw c) >>= unwrap_intermediate
    let t_c ← unwrap_check_error $ Expr.infer c'

    pure { ty' := ty', c' := c', ty_c := t_c }

  let or_throw {α : Type} (msg : String) (x : Option α) : MetaM α :=
    match x with
      | .some e => pure e
      | _ => throwError s!"{msg}: {repr e}"

  match e.all_sk with
  | .some e =>
    Ast.Expr.fromExpr e |> or_throw "unsupported expr; was all SK"
  | _ =>
    match e with
    | .call lhs rhs => do
      let lhs' ← do_translate ctx lhs
      let rhs' ← do_translate ctx lhs

      pure $ .call lhs' rhs'
    
    | .raw e =>
      match e with
      | .lam _ ty (.bvar 0) _ =>
        let ty' ← (do_translate ctx (.raw ty))

        pure SKM[(((((S ty') (ty' ~> ty')) ty') ((K ty') (ty' ~> ty'))) ((K ty') ty'))]
      | .lam _ ty (.app lhs rhs) _ =>
        let { lhs', rhs', ty_lhs, ty_rhs, ty' } ← abstr_app_vars ctx ty lhs rhs

        pure SKM[(((((S ty_lhs) ty_rhs) ty') lhs') rhs')]
      | .forallE _ ty (.bvar 0) _ =>
        let ty' ← do_translate ctx ty

        pure SKM[((((((M S) ty') (ty' ~> ty')) ty') ((K ty') (ty' ~> ty'))) ((K ty') ty'))]
      | .forallE _ ty (.app lhs rhs) _ =>
        let { lhs', rhs', ty_lhs, ty_rhs, ty' } ← abstr_app_vars ctx ty lhs rhs

        pure SKM[((((((M S) ty_lhs) ty_rhs) ty') lhs') rhs')]
      | .lam _ ty (.bvar n) _ =>
        let ty' ← do_translate ctx ty
        let ctx' := ty' :: ctx
        let t_v ← ctx'[n]? |> or_throw s!"missing type #{n} in context"

        pure SKM[((K t_v) ty')]
      | .lam _ ty c _ =>
        let { ty', ty_c, c' } ← abstr_const ctx ty c
        pure SKM[(((K ty_c) ty') c')]
      | .forallE _ ty (.bvar n) _ =>
        let ty' ← do_translate ctx ty
        let ctx' := ty' :: ctx
        let t_v ← ctx'[n]? |> or_throw s!"missing type #{n} in context"

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
  toExpr <$> do_translate [] (IntermediateExpr.fromExpr e)

#eval Expr.infer $ translate (λ (x : Type 1) (y : Type 0) => y)



