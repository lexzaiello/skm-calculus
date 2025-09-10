import Mathlib.Tactic
import Lean
import Lean.Elab.Term

namespace Ast

abbrev Universe := ℕ

inductive Expr {α : Type} where
  | cnst : α        → Expr
  | k    : Universe → Universe → Expr
  | s    : Universe → Universe → Universe → Expr
  | m    : Expr
  | pi   : Expr
  | pi'  : Expr
  | imp  : Expr
  | imp' : Expr
  | ty   : Universe → Expr
  | prp  : Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr, Lean.ToExpr

namespace Expr

def max_universe : @Expr α → Universe
  | .k _m n => max _m n
  | .s _m n o => max (max _m n) o
  | .ty n => n
  | .call lhs rhs => max lhs.max_universe rhs.max_universe
  | _ => 0

end Expr

inductive ExprBox (e : @Ast.Expr α) where
  | mk : ExprBox e

declare_syntax_cat skmexpr
declare_syntax_cat atom
declare_syntax_cat judgment
declare_syntax_cat binder
declare_syntax_cat operator

syntax "domain"   : operator
syntax "codomain" : operator
syntax "self"     : operator
syntax "universe" : operator

syntax "(" ident ":" skmexpr ")"   : binder
syntax ident ":" skmexpr           : binder
syntax ident ":" skmexpr           : binder
syntax "(" skmexpr ":" skmexpr ")" : judgment

syntax "K"    : atom
syntax "M"    : atom
syntax "⤳"   : atom
syntax "→"    : atom
syntax "←"    : atom
syntax "<~"   : atom
syntax "S"    : atom
syntax "Prop" : atom
syntax "Type" : atom
syntax ident           : atom
syntax "(" skmexpr ")" : atom
syntax operator        : atom
syntax judgment        : atom
syntax "?"             : atom
syntax "#" term        : atom
syntax "@" atom        : atom

declare_syntax_cat app
syntax app atom      : app
syntax atom          : app

syntax "λ" binder binder* "=>" skmexpr                 : skmexpr
syntax "∀" binder* "," skmexpr                         : skmexpr
syntax app "⤳" app                                    : skmexpr
syntax app "<~" app                                    : skmexpr
syntax app "→" app                                     : skmexpr
syntax app "←" app                                     : skmexpr
syntax app                                             : skmexpr

syntax "(" term ")" "⟪" skmexpr "⟫"         : term
syntax "SKM" "(" term ")" "[" skmexpr "]"   : term

macro_rules
  | `(SKM ($t:term) [ $e:skmexpr ])  => `((($t) ⟪ $e ⟫ : (@Expr $t)))

macro_rules
  | `(($t_inner:term)⟪ universe (Type #$n:term) ⟫) => `(($n).succ)
  | `(($t_inner:term)⟪ universe ($lhs:app $rhs:atom) ⟫) => do
    let u_lhs ← `(SKM($t_inner)[universe ($lhs)])
    let u_rhs ← `(SKM($t_inner)[universe $rhs])

    pure $ `($u_lhs + $u_rhs)
  | `(($t_inner:term)⟪ universe $e:atom ⟫) => `(Nat.zero)
  | `(($t_inner:term)⟪ M ($_e:skmexpr : $t:skmexpr) ⟫) => pure t
  | `(($t_inner:term)⟪ domain ($t_in:skmexpr ⤳ $_t_out:skmexpr) ⟫) => pure t_in
  | `(($t_inner:term)⟪ codomain ($_t_in:skmexpr ⤳ $t_out:skmexpr) ⟫) => pure t_out
  | `(($t_inner:term)⟪ M (@→ $t₁:atom $t₂:atom) ⟫) => do
    `(SKM($t_inner)[∀ (x : $t₁) (y : $t₂), Type (universe (($t₁) $t₂))])
  | `(($t_inner:term)⟪ @K #$α:term #$β:term ⟫) => `(Expr.k $α $β)
  | `(($t_inner:term)⟪ M (K $α:atom $β:atom) ⟫) => `(SKM($t_inner)[$α → $β → $α])
  | `(($t_inner:term)⟪ M ($f:atom $arg:atom) ⟫) => do
    let t_f ← `(skmexpr| M $f $arg)
    let t_arg ← `(skmexpr| M $arg)
    if ← (`(skmexpr| domain t_f)) ≠ t_arg then
      Lean.Macro.throwError "application type mismatch"
    else
      `(SKM($t_inner)[((codomain $f) $arg)])
  | `(($t_inner:term)⟪ S ? ? $t_z:atom $x:atom ⟫) => do
    let t_x ← `(skmexpr| (M $x))
    `(SKM($t_inner)[(S (codomain (codomain $t_x)) (domain (codomain $t_x)) $t_z $x)])
  | `(($t_inner:term)⟪ @S #$m:term #$n:term #$o:term ⟫) => `(@Expr.s $t_inner $m $n $o)
  | `(($t_inner:term)⟪ @K #$m:term #$n:term ⟫) => `(@Expr.k $t_inner $m $n)
  | `(($t_inner:term)⟪ S $m:atom $n:atom $o:atom ⟫) => `(SKM($t_inner)[((((@S #(($t_inner)⟪$m⟫.max_universe) #(($t_inner)⟪$n⟫.max_universe) #(@($t_inner)⟪$o⟫.max_universe _)) $m) $n) $o)])
  | `(($t_inner:term)⟪ K ? $t_y:atom $e:atom ⟫) => do
    let et ← `(skmexpr| M $e)
    `(SKM($t_inner)[((K $et $t_y) $e)])
  | `(($t_inner:term)⟪ K $m:atom $n:atom ⟫) => `(SKM($t_inner)[(((@K #(@($t_inner)⟪$m⟫.max_universe _) #(@($t_inner)⟪$n⟫.max_universe _)) $m) $n)])
  | `(($t_inner:term)⟪ K ? $t_y:atom $e ⟫) => `(SKM($t_inner)[((K (M $e) $t_y) $e)])
  | `(($t_inner:term)⟪ M ⟫)                            => `(@Expr.m $t_inner)
  | `(($t_inner:term)⟪ ? ⟫)                            => `(@Expr.hole $t_inner)
  | `(($t_inner:term)⟪ Ty #$n:term ⟫)                   => `(@Expr.ty $t_inner $n)
  | `(($t_inner:term)⟪ Prp ⟫)                          => `(@Expr.prp $t_inner)
  | `(($t_inner:term)⟪ ⤳ ⟫)                           => `(@Expr.pi $t_inner)
  | `(($t_inner:term)⟪ <~ ⟫)                           => `(@Expr.pi' $t_inner)
  | `(($t_inner:term)⟪ → ⟫)                            => `(@Expr.imp $t_inner)
  | `(($t_inner:term)⟪ ← ⟫)                            => `(@Expr.imp' $t_inner)
  | `(($t_inner:term)⟪ $e₁:skmexpr ⤳ $e₂:skmexpr ⟫)   => `(SKM($t_inner)[(((⤳) $e₁) $e₂)])
  | `(($t_inner:term)⟪ $e₁:skmexpr <~ $e₂:skmexpr ⟫)   => `(SKM($t_inner)[($e₂ ⤳ $e₁)])
  | `(($t_inner:term)⟪ $e₁:skmexpr → $e₂:skmexpr ⟫)    => `(SKM($t_inner)[∀ (x : $e₁), $e₂])
  | `(($t_inner:term)⟪ $e₁:skmexpr ← $e₂:skmexpr ⟫)    => `(SKM($t_inner)[$e₂ → $e₁])
  | `(($t_inner:term)⟪ $e:ident ⟫)                     => `($e)
  | `(($t_inner:term)⟪ # $e:term ⟫)                    => `($e)
  | `(($t_inner:term)⟪ ($e:skmexpr) ⟫)                 => `(($t_inner)⟪$e⟫)
  -- Accepts an expression of type e, returning type e
  | `(($t_inner:term)⟪ self $e:atom ⟫)                 => `(SKM($t_inner)[(K (M $e) $e $e)])
  | `(($t_inner:term)⟪ λ $_v:ident : $t:skmexpr => $body:skmexpr ⟫) => `(SKM($t_inner)[λ ($_v : $t) => $body])
  | `(($t_inner:term)⟪ λ ($_v:ident : $t:skmexpr) => ($e₁:app $e₂:atom) ⟫)=>
    `(SKM($t_inner)[(S ? ? $t $e₁ $e₂)])
  | `(($t_inner:term)⟪ λ ($_v:ident : $t:skmexpr) => $body:skmexpr ⟫)=> `(SKM($t_inner)[(K ? $t $body)])
  | `(($t_inner:term)⟪ λ ($_v:ident : $t:skmexpr) $tys:binder* => $body:skmexpr ⟫)=>
    match tys.toList with
    | stx::xs => `(SKM($t_inner)[λ ($_v : $t) => (λ $stx $(⟨xs⟩)* => $body)])
    | _ => `(SKM($t_inner)[λ ($_v : $t) => $body])
  | `(($t_inner:term)⟪ $e₁:app $e₂:atom ⟫) => `(@Expr.call $t_inner ($t_inner)⟪$e₁⟫ ($t_inner)⟪$e₂⟫)

namespace Expr

#eval SKM (Unit) [(λ (x : Ty #0) => ((K Ty #0  Ty #0) (K Ty #0 Ty #0)))]

def toStringImpl [ToString α] (e : @Expr α) : String :=
  match e with
  | SKM(α)[(@S #_m #n #o)]  => s!"S.{_m},{n},{o}"
  | SKM(α)[(@K #_m #n)]    => s!"K.{_m},{n}"
  | SKM(α)[M]    => "M"
  | SKM(α)[Ty n] => s!"Type {n}"
  | SKM(α)[Prp]  => "Prop"
  | SKM(α)[?]    => "?"
  | SKM(α)[⤳]  => "⤳"
  | SKM(α)[<~]  => "<~"
  | SKM(α)[→]  => "→"
  | SKM(α)[←]  => "←"
  | SKM(α)[(t_in ⤳ t_out)] => s!"({t_in.toStringImpl} ⤳ {t_out.toStringImpl})"
  | SKM(α)[(lhs rhs)] => s!"({lhs.toStringImpl} {rhs.toStringImpl})"
  | .cnst c => s!"{c}"

instance {α : Type} [ToString α] : ToString (@Expr α) where
  toString := toStringImpl

#eval SKM (Unit) [λ (_v : Ty 1) (_u : Ty 2) => M]

def insert_arrow_arg {α : Type} (in_e e : @Ast.Expr α) : @Ast.Expr α :=
  match in_e with
  | SKM(α)[(t_in ⤳ t_out)] =>
    SKM(α)[(#(insert_arrow_arg t_in e) ⤳ #(insert_arrow_arg t_out e))]
  | x => SKM(α)[(x e)]

def pop_arrow {α : Type} : @Ast.Expr α → @Ast.Expr α
  | SKM(_)[(_t_in ⤳ t_out)] => t_out
  | e => e

end Expr

def mk_k_type {α : Type} (_m n : Universe) : @Ast.Expr α :=
  sorry

end Ast
