import Lean
import SkLean.Ast3
import SkLean.Eval
import SkLean.Checker
open Lean

syntax (name := translate) "translate" term : term

inductive IntermediateExpr where
  | k    : IntermediateExpr
  | s    : IntermediateExpr
  | m    : IntermediateExpr
  | arr  : IntermediateExpr
  | hole : IntermediateExpr
  | ty   : ℕ → IntermediateExpr
  | prp  : IntermediateExpr
  | call : IntermediateExpr → IntermediateExpr → IntermediateExpr
  | lam  : IntermediateExpr → IntermediateExpr → IntermediateExpr
  | var  : ℕ → IntermediateExpr
  | forE : IntermediateExpr → IntermediateExpr → IntermediateExpr
  | skm  : Ast.Expr  → IntermediateExpr
  | intr : IntermediateExpr → IntermediateExpr
deriving BEq, Repr, Lean.ToExpr

namespace IntermediateExpr

def toStringImpl : IntermediateExpr → String
  | .k => "K"
  | .s => "S"
  | .m => "M"
  | .arr => "→"
  | .hole => "_"
  | .ty n => s!"Type {n}"
  | .prp => "Prop"
  | .call lhs rhs => s!"({lhs.toStringImpl} {rhs.toStringImpl})"
  | .lam t body => s!"λ :{t.toStringImpl} => {body.toStringImpl}"
  | .var n => ".var {n}"
  | .intr e => s!"{e.toStringImpl}"
  | .skm e => s!"{e}"
  | .forE t body => s!"∀ :{t.toStringImpl}, {body.toStringImpl}"

end IntermediateExpr

instance : ToString IntermediateExpr where
  toString := IntermediateExpr.toStringImpl

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
syntax "Prp"                      : skmexpr'
syntax "Ty" term                  : skmexpr'
syntax "Typ" num                  : skmexpr'
syntax "#~>"                      : skmexpr'
syntax "_"                        : skmexpr'
syntax skmexpr' "~>" skmexpr'     : skmexpr'
syntax skmexpr' "!~>" skmexpr'    : skmexpr'
syntax "(" skmexpr' skmexpr' ")"  : skmexpr'
syntax ident                      : skmexpr'
syntax "#" term                   : skmexpr'
syntax "(" skmexpr' ")"           : skmexpr'
syntax "λ" skmexpr' "=>" skmexpr' : skmexpr'
syntax "∀" skmexpr' "," skmexpr'  : skmexpr'
syntax "!" skmexpr'               : skmexpr'

syntax " {{ " skmexpr' " }} "     : term
syntax "SKM`[ " skmexpr' " ] "    : term

macro_rules
  | `(SKM`[ $e:skmexpr' ]) => `({{ $e }})

macro_rules
  | `({{ !$e:skmexpr' }})                    => `(IntermediateExpr.intr {{ $e }})
  | `({{ K }})                               => `(IntermediateExpr.k)
  | `({{ S }})                               => `(IntermediateExpr.s)
  | `({{ M }})                               => `(IntermediateExpr.m)
  | `({{ _ }})                               => `(IntermediateExpr.hole)
  | `({{ Ty $n:term }})                      => `(IntermediateExpr.ty $n)
  | `({{ Typ $n:num }})                      => `(IntermediateExpr.ty $n)
  | `({{ Prp }})                             => `(IntermediateExpr.prp)
  | `({{ λ $t:skmexpr' => $body:skmexpr' }}) => `(IntermediateExpr.lam {{$t}}  {{$body}})
  | `({{ ∀ $t:skmexpr', $body:skmexpr' }})   => `(IntermediateExpr.forE {{$t}} {{$body}})
  | `({{ #~> }})                             => `(IntermediateExpr.arr)
  | `({{ $e₁:skmexpr' ~> $e₂:skmexpr' }})    => `(IntermediateExpr.call (IntermediateExpr.call IntermediateExpr.arr {{ $e₁ }}) {{ $e₂ }})
  | `({{ $e₁:skmexpr' !~> $e₂:skmexpr' }})   => `(SKM`[$e₁ ~> (((K $e₂) $e₁) $e₂)])
  | `({{ $e:ident }})                        => `($e)
  | `({{ # $e:term }})                       => `($e)
  | `({{ ($e:skmexpr') }})                   => `({{$e}})
  | `({{ ($e₁:skmexpr' $e₂:skmexpr') }})     => `(IntermediateExpr.call {{ $e₁ }} {{ $e₂ }})

namespace IntermediateExpr

def all_human_sk (e : IntermediateExpr) : Bool :=
  match e with
  | SKM`[S]         => true
  | SKM`[K]         => true
  | SKM`[M]         => true
  | SKM`[(lhs rhs)] => all_human_sk lhs ∧ all_human_sk rhs
  | SKM`[#~>]       => true
  | SKM`[Prp]       => true
  | SKM`[_]         => true
  | SKM`[Ty _]      => true
  | _               => false

def all_sk (e : IntermediateExpr) : Except IntermediateExpr Ast.Expr :=
  match e with
  | .skm e          => pure e
  | SKM`[S]         => pure SKM[S]
  | SKM`[K]         => pure SKM[K]
  | SKM`[M]         => pure SKM[M]
  | SKM`[Prp]       => pure SKM[Prp]
  | SKM`[_]         => pure SKM[_]
  | SKM`[Ty n]      => pure SKM[Ty n]
  | SKM`[(lhs rhs)] => do
    let lhs' ← lhs.all_sk
    let rhs' ← rhs.all_sk

    pure SKM[(lhs' rhs')]
  | SKM`[#~>] => pure SKM[#~>]
  | .intr e => e.all_sk
  | e => .error e

partial def infer' : List IntermediateExpr → IntermediateExpr → Except (@TypeError IntermediateExpr) IntermediateExpr
  | ctx, e@(.var n)
  | ctx, (.intr e@(.var n)) => match ctx[n]? with
    | .some e => pure e
    | .none => .error (.no_type_not_comb e)
  | ctx, e =>
    match e.all_sk with
    | .ok e => match Expr.infer_unsafe e with
      | .ok e => .ok (.skm e)
      | .error (.argument_mismatch a b c d) => .error $ .argument_mismatch (.skm a) (.skm b) (.skm c) (.skm d)
      | .error (.no_type_not_comb e) => .error $ .no_type_not_comb (.skm e)
      | .error (.bad_type_not_comb at_e in_e t) => .error $ .bad_type_not_comb (.skm at_e) (.skm in_e) (.skm t)
    | _ =>
      match e with
      | SKM`[(lhs rhs)]
      | SKM`[!(lhs rhs)] => do
        let t_lhs ← infer' ctx lhs

        pure SKM`[(t_lhs rhs)]
      | e => .error (.no_type_not_comb e)

def from_expr : Lean.Expr → Except Lean.Expr IntermediateExpr
  | .const `IntermediateExpr.k []     => pure .k
  | .const `IntermediateExpr.s []     => pure .s
  | .const `IntermediateExpr.m []     => pure .m
  | .const `IntermediateExpr.arr []   => pure .arr
  | .const `IntermediateExpr.hole []  => pure .hole
  | .app
    (.const `IntermediateExpr.ty [])
    (.lit (.natVal n)) => pure $ .ty n
  | .const `IntermediateExpr.prp []   => pure .prp
  | (.app (.app (.const `IntermediateExpr.call []) lhs) rhs) => do
    let lhs' ← from_expr lhs
    let rhs' ← from_expr rhs

    pure SKM`[(lhs' rhs')]
  | (.app (.app (.const `IntermediateExpr.lam []) t) body) => do
    let t ← from_expr t
    let body ← from_expr body

    pure SKM`[(λ t => body)]
  | (.app (.app (.const `IntermediateExpr.forE []) t) body) => do
    let t ← from_expr t
    let body ← from_expr body

    pure SKM`[(∀ t, body)]
  | .bvar n           => pure $ .var n
  | .const `Ast.Expr.k [] => pure SKM`[K]
  | .const `Ast.Expr.s [] => pure SKM`[S]
  | .const `Ast.Expr.m [] => pure SKM`[M]
  | (.app (.const `Ast.Expr.ty []) (.lit (.natVal n))) => pure SKM`[Ty n]
  | (.app (.const `Ast.Expr.ty []) (.app (.app (.app (.const `OfNat.ofNat []) _ty) (.lit (.natVal n))) _inst)) =>
    pure SKM`[Ty n]
  | (.const `Ast.Expr.prp []) => pure SKM`[Prp]
  | .sort .zero => pure SKM`[Prp]
  | .sort n     => pure SKM`[Ty n.depth.pred]
  | (.app (.app (.const `Ast.Expr.call []) lhs) rhs) => do
    let lhs' ← from_expr lhs
    let rhs' ← from_expr rhs

    pure SKM`[(lhs' rhs')]
  | .const `Ast.Expr.arr [] => pure SKM`[#~>]
  | .lam _ t body _     => do
    let t'    ← from_expr t
    let body' ← from_expr body

    pure $ SKM`[λ t' => body']
  | .forallE _ t body _ => do
    let t'    ← from_expr t
    let body' ← from_expr body

    pure $ SKM`[∀ t', body']
  | .app lhs rhs => do
    let lhs' ← from_expr lhs
    let rhs' ← from_expr rhs

    pure $ SKM`[(lhs' rhs')]
  | e  => .error e

def shift_down_from : ℕ →  IntermediateExpr → IntermediateExpr
  | j, v@(.var i)      => if i > j then (.var i.pred) else v
  | j, (.call lhs rhs) => SKM`[(#(lhs.shift_down_from j)  #(rhs.shift_down_from j))]
  | j, .lam  t b       => SKM`[λ #(t.shift_down_from j.succ) => #(b.shift_down_from j.succ)]
  | j, .forE t b       => SKM`[∀ #(t.shift_down_from j.succ), #(b.shift_down_from j.succ)]
  | _, x               => x

def free_in : ℕ → IntermediateExpr → Bool
  | j, (.var i) => i == j
  | j, (.call f x) => free_in j f || free_in j x
  | j, SKM`[λ t => body] | j, SKM`[!(λ t => body)] => free_in j.succ t || free_in j.succ body
  | j, SKM`[∀ t, body] | j, SKM`[!(∀ t, body)] => free_in j.succ t || free_in j.succ body
  | _, _ => false

end IntermediateExpr

def or_throw {α : Type} (msg : String) : Option α → MetaM α
  | .some e => pure e
  | _ => throwError msg

def unwrap_check_error {α : Type} [ToString α] : Except (@TypeError α) α → MetaM α
  | .ok e => pure e
  | e     => throwError s!"typechecker error: {e}"

def unwrap_intermediate (e : IntermediateExpr) : MetaM Ast.Expr :=
    match e.all_sk with
    | .ok e     => pure e
    | .error e  => throwError s!"expected SKM expression, found {repr e}"

inductive AbstractMode where
  | m : AbstractMode
  | e : AbstractMode

partial def abstract : AbstractMode → List IntermediateExpr → ℕ → IntermediateExpr → MetaM IntermediateExpr
  | mode, ctx@(t::_), j, (.var i) => do
    let ty ← ctx[i]? |> or_throw s!"missing type #{i} in context"

    if i == j then
      let pre := match mode with
        | .e => SKM`[!S]
        | .m => SKM`[!(M S)]
      pure SKM`[!(((((pre (ty !~> (ty !~> ty) !~> ty)) (ty !~> ty !~> ty)) ty) ((K ty) (ty !~> ty))) ((K ty) ty))]
    else
      let pre := match mode with
        | .e => SKM`[K]
        | .m => SKM`[(M K)]
      pure SKM`[!(((pre ty) t) #(.var (if i > j then i.pred else i)))]
  | mode, c@(t::_), j, e@SKM`[(lhs rhs)]
  | mode, c@(t::_), j, e@SKM`[!(lhs rhs)] => do
    if e.all_human_sk then
      pure e
    else
      let l ← abstract .e c j lhs
      let r ← abstract .e c j rhs

      let t_lhs ← unwrap_check_error (l.infer' c)
      let t_rhs ← unwrap_check_error (r.infer' c)

      let pre := match mode with
        | .e => SKM`[!S]
        | .m => SKM`[!(M S)]

      pure SKM`[!(((((pre t_lhs) t_rhs) t) l) r)]
  | mode, c@(t::_), j, e => do
    let t_e ← unwrap_check_error $ e.infer' c

    if e.all_human_sk then
      pure e
    else
      let pre := match mode with
        | .e => SKM`[!K]
        | .m => SKM`[!(M K)]

      pure SKM`[!(((pre t_e) t) e)]
  | _, _, _, _ => throwError "context empty"

def do_translate (ctx : List IntermediateExpr) (e : IntermediateExpr) : MetaM IntermediateExpr := do
  match e.all_sk with
  | .ok e => pure $ .skm e
  | _ => go ctx 0 e
  where go : List IntermediateExpr → ℕ → IntermediateExpr → MetaM IntermediateExpr
    | ctx, lvl, SKM`[(λ t => body)]
    | ctx, lvl, SKM`[!(λ t => body)] => do
      let t'    ← go ctx lvl.succ t
      let body' ← go (t'::ctx) lvl.succ body

      abstract .e (t'::ctx) 0 body'
    | ctx, lvl, SKM`[(∀ t, body)]
    | ctx, lvl, SKM`[!(∀ t, body)] => do
      let t'    ← go ctx lvl.succ t
      let body' ← go (t'::ctx) lvl.succ body

      abstract .m (t'::ctx) 0 body'
    | ctx, lvl, SKM`[(lhs rhs)]
    | ctx, lvl, SKM`[!(lhs rhs)] => do
      let lhs' ← go ctx lvl lhs
      let rhs' ← go ctx lvl rhs

      pure $ SKM`[(lhs' rhs')]
    | _, _, e => pure e

def compile (e : IntermediateExpr) : MetaM Ast.Expr := do match (← IntermediateExpr.all_sk <$> do_translate [] e) with
  | .ok e => pure e
  | .error e => throwError "err: {e}"

elab "translate" e:term : term => do
  let e ← Elab.Term.elabTerm e .none
  match IntermediateExpr.from_expr e with
  | .ok e => match (← IntermediateExpr.all_sk <$> do_translate [] e) with
    | .ok e      => pure $ toExpr e
    | .error e   => throwError "couldn't convert back to Lean: {repr e}"
  | .error e => throwError s!"parsing failed: {repr e}"

#eval Expr.infer_unsafe $ translate ((λ (x : Type 1) => x) (Type 0))
#eval Expr.infer_unsafe $ translate ((λ (x : Type 1) (y : x) => y) (Type 0 → Type 0) (λ (p : Type 0) => p))

