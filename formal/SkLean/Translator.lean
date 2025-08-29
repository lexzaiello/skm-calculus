import Lean
import SkLean.Ast3
import SkLean.UnsafeEval
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

inductive TypeError where
  | argument_mismatch (expected actual in_e : Ast.Expr) : TypeError
  | no_type_not_comb  (at_e : Ast.Expr)                 : TypeError

instance : ToString TypeError where
  toString
  | .argument_mismatch expected actual in_e => s!"Argument type mismatch in function application of {in_e}. Expected {expected}, but found {actual}"
  | .no_type_not_comb at_e => s!"type inference failed for {at_e}, but not a combinator"

def is_typed_comb : Ast.Expr → Bool
  | SKM[K]
  | SKM[M]
  | SKM[S]
  | SKM[(K _α)]
  | SKM[(S _α)]
  | SKM[((S _α) _β)]
  | SKM[#~>]
  | SKM[(#~> _t_in)] => true
  | SKM[(M e)] => is_typed_comb e
  | _ => false

def add_m : Ast.Expr → Ast.Expr
  | SKM[M]    => SKM[(M M)]
  | SKM[K]    => SKM[(M K)]
  | SKM[S]    => SKM[(M S)]
  | SKM[#~>]  => SKM[(M #~>)]
  | SKM[Ty n] => SKM[(M (Ty n))]
  | SKM[(lhs rhs)] => SKM[((#(add_m lhs)) rhs)]

def eval_once : Ast.Expr → Option Ast.Expr
  | SKM[((((K _α) _β) x) _y)] => pure x
  | SKM[((((((S _α) _β) _γ) x) y) z)] => pure SKM[((x z) (y z))]
  | SKM[(((M K) α) β)]     => pure SKM[(α ~> (β ~> α))]
  | SKM[((((M S) α) β) γ)] => pure SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | SKM[(M (Ty n))] => pure SKM[Ty n.succ]
  | SKM[((M t_in) ~> t_out)] => pure SKM[(t_in ~> (M t_out))]
  | SKM[(M (lhs rhs))] => pure SKM[((M lhs) rhs)]
  | SKM[((_t_in ~> t_out) _arg)] => t_out
  | x => x

def infer : Ast.Expr → Except TypeError Ast.Expr
  | SKM[K]               => pure SKM[(M K)]
  | SKM[S]               => pure SKM[(M S)]
  | SKM[M]               => pure SKM[(M M)]
  | SKM[Ty n]            => pure SKM[Ty n.succ]
  | SKM[#~>]             => pure SKM[(M #~>)]
  | SKM[(M e)] => infer e
  | SKM[(t_in ~> t_out)] => do
    pure SKM[(t_in ~> #(← infer t_out))]
  | SKM[(lhs rhs)]       => do
    let t_lhs ← infer lhs
    match t_lhs with
    | SKM[(t_in ~> t_out)] =>
      let found ← infer rhs

      if found == t_in then
        pure t_out
      else
        .error $ .argument_mismatch t_in t_lhs lhs
    | e =>
      if is_typed_comb e then
        let with_m := SKM[((#(add_m lhs)) rhs)]
        pure $ (eval_once with_m).getD with_m
      else
        .error $ .no_type_not_comb lhs

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

