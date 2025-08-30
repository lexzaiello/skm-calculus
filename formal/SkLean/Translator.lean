import Lean
import SkLean.Ast3
import SkLean.UnsafeEval
import SkLean.Eval
import SkLean.Checker
open Lean

syntax (name := translate) "translate" term : term

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

structure AppInfo where
  lhs'   : IntermediateExpr
  rhs'   : IntermediateExpr
  ty_lhs : IntermediateExpr
  ty_rhs : IntermediateExpr
  ty'    : IntermediateExpr

structure ConstInfo where
  ty'    : IntermediateExpr
  ty_c   : IntermediateExpr
  c'     : IntermediateExpr

declare_syntax_cat skmexpr'
syntax "K"                        : skmexpr'
syntax "S"                        : skmexpr'
syntax "M"                        : skmexpr'
syntax "#~>"                      : skmexpr'
syntax skmexpr' "~>" skmexpr'     : skmexpr'
syntax "(" skmexpr' skmexpr' ")"  : skmexpr'
syntax ident                      : skmexpr'
syntax "Ty" term                  : skmexpr'
syntax "#" term                   : skmexpr'
syntax "(" skmexpr' ")"           : skmexpr'
syntax "λ" skmexpr' "=>" skmexpr' : skmexpr'
syntax "∀" skmexpr' "," skmexpr'  : skmexpr'

syntax " {{ " skmexpr' " }} "     : term
syntax "SKM'[ " skmexpr' " ] "    : term

macro_rules
  | `(SKM'[ $e:skmexpr' ]) => `({{ $e }})

macro_rules
  | `({{ K }})                               => `(IntermediateExpr.k)
  | `({{ S }})                               => `(IntermediateExpr.s)
  | `({{ M }})                               => `(IntermediateExpr.m)
  | `({{ Ty $n:term }})                      => `(IntermediateExpr.ty $n)
  | `({{ λ $t:skmexpr' => $body:skmexpr' }}) => `(IntermediateExpr.lam {{$t}}  {{$body}})
  | `({{ ∀ $t:skmexpr', $body:skmexpr' }})   => `(IntermediateExpr.forE {{$t}} {{$body}})
  | `({{ #~> }})                             => `(IntermediateExpr.arr)
  | `({{ $e₁:skmexpr' ~> $e₂:skmexpr' }})    => `(IntermediateExpr.call (IntermediateExpr.call IntermediateExpr.arr {{ $e₁ }}) {{ $e₂ }})
  | `({{ $e:ident }})                        => `($e)
  | `({{ # $e:term }})                       => `($e)
  | `({{ ($e:skmexpr') }})                   => `({{$e}})
  | `({{ ($e₁:skmexpr' $e₂:skmexpr') }})     => `(IntermediateExpr.call {{ $e₁ }} {{ $e₂ }})

namespace IntermediateExpr

def all_sk (e : IntermediateExpr) : Option Ast.Expr :=
  match e with
  | .skm e          => pure e
  | SKM'[S]         => pure SKM[S]
  | SKM'[K]         => pure SKM[K]
  | SKM'[M]         => pure SKM[M]
  | SKM'[Ty n]      => pure SKM[Ty n]
  | SKM'[(lhs rhs)] => do
    let lhs' ← lhs.all_sk
    let rhs' ← rhs.all_sk

    pure SKM[(lhs' rhs')]
  | SKM'[#~>] => SKM[#~>]
  | _ => .none

def from_expr : Lean.Expr → Except Lean.Expr IntermediateExpr
  | .const `Expr.k [] => pure SKM'[S]
  | .const `Expr.s [] => pure SKM'[K]
  | .const `Expr.m [] => pure SKM'[M]
  | (.app (.const `Expr.ty []) (.lit (.natVal n))) => pure $ .ty n
  | .const `Expr.arr [] => pure SKM'[#~>]
  | .sort t             => pure $ SKM'[Ty (t.depth.pred)]
  | .lam _ t body _     => do
    let t'    ← from_expr t
    let body' ← from_expr body

    pure $ SKM'[λ t' => body']
  | .forallE _ t body _ => do
    let t'    ← from_expr t
    let body' ← from_expr body

    pure $ SKM'[∀ t', body']
  | .app lhs rhs => do
    let lhs' ← from_expr lhs
    let rhs' ← from_expr rhs

    pure $ SKM'[(lhs' rhs')]
  | e  => .error e

def shift_down_from : ℕ →  IntermediateExpr → IntermediateExpr
  | j, v@(.var i)      => if i > j then (.var i.pred) else v
  | j, (.call lhs rhs) => SKM'[(#(lhs.shift_down_from j)  #(rhs.shift_down_from j))]
  | j, .lam  t b       => SKM'[λ #(t.shift_down_from j.succ) => #(b.shift_down_from j.succ)]
  | j, .forE t b       => SKM'[∀ #(t.shift_down_from j.succ), #(b.shift_down_from j.succ)]
  | _, x               => x

end IntermediateExpr

partial def do_translate (ctx : List IntermediateExpr) (e : IntermediateExpr) : MetaM IntermediateExpr := do
  let unwrap_check_error : Except TypeError Ast.Expr → MetaM Ast.Expr
    | .ok e => pure e
    | e     => throwError s!"typechecker error: {e}"

  let unwrap_parse : Except Lean.Expr IntermediateExpr → MetaM IntermediateExpr
    | .ok e => pure e
    | e     => throwError s!"unparseable expression: {repr e}"

  let unwrap_intermediate (e : IntermediateExpr) : MetaM Ast.Expr :=
    match e.all_sk with
    | .some e => pure e
    | _       => throwError s!"expected SKM expression, found {repr e}"

  let do_trans (ctx : List IntermediateExpr) (e : IntermediateExpr) : MetaM IntermediateExpr :=
    do_translate ctx e

  let abstr_app_vars (ctx : List IntermediateExpr) (ty lhs rhs : IntermediateExpr) : MetaM AppInfo := do
    let ty'    ← do_trans ctx ty
    let ctx' := (ty' :: ctx)
    let lhs'   ← (do_trans ctx' lhs)
    let rhs'   ← (do_trans ctx' rhs)
    let ty_lhs ← unwrap_check_error $ Expr.infer (← unwrap_intermediate lhs')
    let ty_rhs ← unwrap_check_error $ Expr.infer (← unwrap_intermediate rhs')

    pure { lhs' := lhs', rhs' := rhs', ty_lhs := (.skm ty_lhs), ty_rhs := (.skm ty_rhs), ty' := ty' }

  let abstr_const (ctx : List IntermediateExpr) (ty c : IntermediateExpr) : MetaM ConstInfo := do
    let ty' ← (do_trans ctx ty)
    let ctx' := (ty' :: ctx)
    let c' ← (do_trans ctx' c)
    let t_c ← unwrap_check_error $ Expr.infer (← unwrap_intermediate c')

    pure { ty' := ty', c' := c', ty_c := (.skm t_c) }

  let or_throw {α : Type} (msg : String) (x : Option α) : MetaM α :=
    match x with
      | .some e => pure e
      | _ => throwError s!"{msg}: {repr e}"

  match e.all_sk with
  | .some e => pure $ .skm e
  | _ =>
    match e with
    | SKM'[(lhs rhs)] => do
      let lhs' ← do_translate ctx lhs
      let rhs' ← do_translate ctx lhs

      pure $ SKM'[(lhs' rhs')]
    | SKM'[λ ty => #(.var 0)] =>
      let ty' ← (do_translate ctx ty)

      pure SKM'[(((((S ty') (ty' ~> ty')) ty') ((K ty') (ty' ~> ty'))) ((K ty') ty'))]
    | SKM'[λ ty => (lhs rhs)] =>
      let { lhs', rhs', ty_lhs, ty_rhs, ty' } ← abstr_app_vars ctx ty lhs rhs

      pure SKM'[(((((S ty_lhs) ty_rhs) ty') lhs') rhs')]
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



