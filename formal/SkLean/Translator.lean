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
  | intr : IntermediateExpr → IntermediateExpr
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
syntax "!" skmexpr'               : skmexpr'

syntax " {{ " skmexpr' " }} "     : term
syntax "SKM'[ " skmexpr' " ] "    : term

macro_rules
  | `(SKM'[ $e:skmexpr' ]) => `({{ $e }})

macro_rules
  | `({{ !$e:skmexpr' }})                    => `(IntermediateExpr.intr {{ $e }})
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

def all_human_sk (e : IntermediateExpr) : Bool :=
  match e with
  | SKM'[S]         => true
  | SKM'[K]         => true
  | SKM'[M]         => true
  | SKM'[Ty n]      => true
  | SKM'[(lhs rhs)] => all_human_sk lhs ∧ all_human_sk rhs
  | SKM'[#~>]       => true
  | _               => false

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
  | .intr e => e.all_sk
  | _ => .none

def from_expr : Lean.Expr → Except Lean.Expr IntermediateExpr
  | .bvar n           => pure $ .var n
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

def free_in : ℕ → IntermediateExpr → Bool
  | j, (.var i) => i == j
  | j, (.call f x) => free_in j f || free_in j x
  | j, SKM'[λ t => body] | j, SKM'[!(λ t => body)] => free_in j.succ t || free_in j.succ body
  | j, SKM'[∀ t, body] | j, SKM'[!(∀ t, body)] => free_in j.succ t || free_in j.succ body
  | _, _ => false

end IntermediateExpr

def or_throw {α : Type} (msg : String) (x : Option α) : MetaM α :=
    match x with
      | .some e => pure e
      | _ => throwError msg

def unwrap_check_error : Except TypeError Ast.Expr → MetaM Ast.Expr
    | .ok e => pure e
    | e     => throwError s!"typechecker error: {e}"

def unwrap_intermediate (e : IntermediateExpr) : MetaM Ast.Expr :=
    match e.all_sk with
    | .some e => pure e
    | _       => throwError s!"expected SKM expression, found {repr e}"

inductive AbstractMode where
  | m : AbstractMode
  | e : AbstractMode

def abstract : AbstractMode → List IntermediateExpr → ℕ → IntermediateExpr → MetaM IntermediateExpr
  | mode, ctx@(t::_), j, e@SKM'[(lhs #(.var i))]
  | mode, ctx@(t::_), j, e@SKM'[!(lhs #(.var i))] =>
    if i == j && ¬ (lhs.free_in j) then
      pure $ lhs.shift_down_from j
    else do
      pure e
  | mode, ctx@(t::_), j, (.var i) => do
    let ty ← ctx[i]? |> or_throw s!"missing type #{i} in context"

    if i == j then
      let pre := match mode with
        | .e => SKM'[!S]
        | .m => SKM'[!(M S)]
      pure SKM'[!(((((pre ty) (ty ~> ty)) ty) ((K ty) (ty ~> ty))) ((K ty) ty))]
    else
      let pre := match mode with
        | .e => SKM'[K]
        | .m => SKM'[(M K)]
      pure SKM'[!(((pre ty) t) #(.var (if i > j then i.pred else i)))]
  | mode, c@(t::_), j, e@SKM'[(lhs rhs)]
  | mode, c@(t::_), j, e@SKM'[!(lhs rhs)] => do
    if e.all_human_sk then
      pure e
    else
      let l ← abstract .e c j lhs
      let r ← abstract .e c j rhs

      let t_lhs ← unwrap_intermediate l >>= (unwrap_check_error ∘ Expr.infer)
      let t_rhs ← unwrap_intermediate r >>= (unwrap_check_error ∘ Expr.infer)

      let pre := match mode with
        | .e => SKM'[!S]
        | .m => SKM'[!(M S)]

      pure SKM'[!(((((pre #(.skm t_lhs)) #(.skm t_rhs)) t) l) r)]
  | mode, c@(t::_), j, e => do
    let t_e ← unwrap_intermediate e >>= (unwrap_check_error ∘ Expr.infer)

    if e.all_human_sk then
      pure e
    else
      let pre := match mode with
        | .e => SKM'[!K]
        | .m => SKM'[!(M K)]

      pure SKM'[!(((pre #(.skm t_e)) t) e)]
  | _, _, _, _ => throwError "context empty"

partial def do_translate (ctx : List IntermediateExpr) (e : IntermediateExpr) : MetaM IntermediateExpr := do
  match e.all_sk with
  | .some e => pure $ .skm e
  | _ => go ctx 0 e
  where go : List IntermediateExpr → ℕ → IntermediateExpr → MetaM IntermediateExpr
    | ctx, lvl, SKM'[(λ t => body)]
    | ctx, lvl, SKM'[!(λ t => body)] => do
      let t'    ← go ctx lvl.succ t
      let body' ← go (t'::ctx) lvl.succ body

      abstract .e (t'::ctx) 0 body'
    | ctx, lvl, SKM'[(∀ t, body)]
    | ctx, lvl, SKM'[!(∀ t, body)] => do
      let t'    ← go ctx lvl.succ t
      let body' ← go (t'::ctx) lvl.succ body

      abstract .m (t'::ctx) 0 body'
    | ctx, lvl, SKM'[(lhs rhs)]
    | ctx, lvl, SKM'[!(lhs rhs)] => do
      let lhs' ← go ctx lvl lhs
      let rhs' ← go ctx lvl rhs

      pure $ SKM'[(lhs' rhs')]
    | _, _, e => pure e

elab "translate" e:term : term => do
  let ⟨e, _⟩ ← (Elab.Term.elabTerm e .none).run
  match IntermediateExpr.from_expr e with
  | .ok e => match (← IntermediateExpr.all_sk <$> do_translate [] e) with
    | .some e => pure $ toExpr e
    | .none   => throwError "couldn't convert back to Lean"
  | .error e => throwError s!"parsing failed: {repr e}"

#eval Expr.infer $ translate (λ (x : Type 1) (y : Type 0) => x)



