import SkLean.Ast3

open Ast.Expr

namespace Ast

namespace Expr

declare_syntax_cat skmexpr
declare_syntax_cat atom
declare_syntax_cat judgment
declare_syntax_cat binder
declare_syntax_cat operator
declare_syntax_cat app

syntax "domain"   : operator
syntax "codomain" : operator
syntax "universe" : operator

syntax "(" ident ":" skmexpr ")"   : binder
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

syntax "λ" binder binder* "=>" skmexpr             : skmexpr
syntax "∀" binder* "," skmexpr                     : skmexpr
syntax skmexpr "⤳" skmexpr                        : skmexpr
syntax skmexpr "<~" skmexpr                        : skmexpr
syntax skmexpr "→" skmexpr                         : skmexpr
syntax skmexpr "←" skmexpr                         : skmexpr
syntax skmexpr atom                                : skmexpr
syntax atom                                        : skmexpr
syntax "a!" atom                                   : skmexpr

syntax "(" term ")" "⟪" skmexpr "⟫"         : term
syntax "(" term ")" "⟪₀" atom "⟫"           : term
syntax "SKM" "(" term ")" "[" skmexpr "]"   : term

macro_rules
  | `(SKM ($t:term) [ $e:skmexpr ])  => `((($t) ⟪ $e ⟫ : (@Expr $t)))

macro_rules
  | `(($t_inner:term)⟪₀ ($e:skmexpr) ⟫) => `(($t_inner)⟪ $e ⟫)
  | `(($t_inner:term)⟪₀ ⤳ ⟫) => `(@Expr.pi $t_inner)
  | `(($t_inner:term)⟪₀ <~ ⟫) => `(@Expr.pi' $t_inner)
  | `(($t_inner:term)⟪₀ → ⟫) => `(@Expr.imp $t_inner)
  | `(($t_inner:term)⟪₀ ← ⟫) => `(@Expr.imp' $t_inner)
  | `(($t_inner:term)⟪ $e₁:skmexpr ⤳ $e₂:skmexpr ⟫) => `(SKM($t_inner)[(⤳) ($e₁) ($e₂)])
  | `(($t_inner:term)⟪ $e₁:skmexpr <~ $e₂:skmexpr ⟫) => `(SKM($t_inner)[$e₂ ⤳ $e₁])
  | `(($t_inner:term)⟪ $e₁:skmexpr → $e₂:skmexpr ⟫) => `(SKM($t_inner)[∀ (x : $e₁), $e₂])
  | `(($t_inner:term)⟪ $e₁:skmexpr ← $e₂:skmexpr ⟫) => `(SKM($t_inner)[$e₂ → $e₁])
  | `(($t_inner:term)⟪ universe ($e:skmexpr) ⟫) => `(Expr.max_universe ($t_inner)⟪ $e ⟫)
  | `(($t_inner:term)⟪ universe $e:atom ⟫)      => `(Expr.max_universe ($t_inner)⟪₀ $e ⟫)
  | `(($t_inner:term)⟪ M ($_e:skmexpr : $t:skmexpr) ⟫) => pure t
  | `(($t_inner:term)⟪ domain ($t_in:skmexpr ⤳ $t_out:skmexpr) ⟫) => pure t_in
  | `(($t_inner:term)⟪ codomain ($t_in:skmexpr ⤳ $t_out:skmexpr) ⟫) => pure t_out
  | `(($t_inner:term)⟪ ∀ ($i:ident : $t:skmexpr), $body:skmexpr ⟫) => `(SKM($t_inner)[$t → $body])
  | `(($t_inner:term)⟪₀ M ⟫)                           => `(@Expr.m $t_inner)
  | `(($t_inner:term)⟪₀ ? ⟫)                           => `(@Expr.hole $t_inner)
  | `(($t_inner:term)⟪ Type #$n:term ⟫)                => `(@Expr.ty $t_inner $n)
  | `(($t_inner:term)⟪₀ Prp ⟫)                         => `(@Expr.prp $t_inner)
  | `(($t_inner:term)⟪₀ $e:ident ⟫)                    => `($e)
  | `(($t_inner:term)⟪₀ # $e:term ⟫)                   => `($e)
  | `(($t_inner:term)⟪ M (@→ $t₁:atom $t₂:atom) ⟫)    => `(SKM($t_inner)[a!$t₁ → a!$t₂ → Type (universe (a!$t₁ $t₂))])
  | `(($t_inner:term)⟪ M (K $α:atom $β:atom) ⟫)       => `(SKM($t_inner)[a!$α → a!$β → a!$α])
  | `(($t_inner:term)⟪ M ($f:skmexpr $arg:atom) ⟫) => do
    let t_f ← `(skmexpr| M ($f) $arg)
    let t_arg ← `(($t_inner)⟪ M $arg ⟫)
    if (← `(($t_inner)⟪ domain ($t_f)⟫)) != t_arg then
      Lean.Macro.throwError "application type mismatch"
    else
      `(($t_inner)⟪ (codomain ($f)) $arg⟫)
  | `(($t_inner:term)⟪ @S $m:atom $n:atom $o:atom ⟫) => `(@Expr.s $t_inner ($t_inner)⟪₀ $m⟫ ($t_inner)⟪₀ $n⟫ ($t_inner)⟪₀ $o⟫)
  | `(($t_inner:term)⟪ @K $m:atom $n:atom ⟫) => `(@Expr.k $t_inner ($t_inner)⟪₀ $m⟫ ($t_inner)⟪₀ $n⟫)
  | `(($t_inner:term)⟪ S $m:atom $n:atom $o:atom ⟫) => `(($t_inner)⟪ @S (universe $m) (universe $n) (universe $o) $m $n $o ⟫)
  | `(($t_inner:term)⟪ S ? ? $t_z:atom $x:atom ⟫) => do
    let t_x ← `(skmexpr| M $x)
    `(($t_inner)⟪ S (codomain (codomain ($t_x))) (domain (codomain ($t_x))) $t_z $x⟫)
  | `(($t_inner:term)⟪ K ? $t_y:atom $e:atom ⟫) => `(SKM($t_inner)[K (M $e) $t_y $e])
  | `(($t_inner:term)⟪ K $m:atom $n:atom ⟫) => `(($t_inner)⟪ @K (universe $m) (universe $n) ⟫)
  | `(($t_inner:term)⟪ $e₁:skmexpr $e₂:atom ⟫) => `(@Expr.call $t_inner ($t_inner)⟪$e₁⟫ ($t_inner)⟪₀ $e₂⟫)
  | `(($t_inner:term)⟪ ∀ ($i:ident : $t:skmexpr) $tys:binder*, $body:skmexpr ⟫) => `(SKM($t_inner)[∀ ($i : $t), λ (_x : $t) => $body])
  | `(($t_inner:term)⟪ λ $_v:ident : $t:skmexpr => $body:skmexpr ⟫) => `(SKM($t_inner)[λ ($_v : $t) => $body])
  | `(($t_inner:term)⟪ λ ($_v:ident : $t:skmexpr) => $e₁:skmexpr $e₂:atom ⟫)=>
    `(SKM($t_inner)[(S ? ? ($t) ($e₁) $e₂)])
  | `(($t_inner:term)⟪ λ ($_v:ident : $t:skmexpr) => $body:skmexpr ⟫)=> `(SKM($t_inner)[(K ? ($t) ($body))])
  | `(($t_inner:term)⟪ λ ($_v:ident : $t:skmexpr) $tys:binder* => $body:skmexpr ⟫)=>
    match tys.toList with
    | stx::xs => `(SKM($t_inner)[λ ($_v : $t) => (λ $stx $(⟨xs⟩)* => $body)])
    | _ => `(SKM($t_inner)[λ ($_v : $t) => $body])
  | `(($t_inner:term)⟪ ($e:atom) ⟫) => `(($t_inner)⟪₀ $e⟫)
  | `(($t_inner:term)⟪ ($e:skmexpr) ⟫)  => `(($t_inner)⟪ $e ⟫)

#eval SKM(Unit)[(Type #0) ⤳ (Type #0)]

def toStringImpl [ToString α] (e : @Expr α) : String :=
  match e with
  | SKM(α)[(@S #_m #n #o)]  => s!"S.{_m},{n},{o}"
  | SKM(α)[(@K #_m #n)]    => s!"K.{_m},{n}"
  | SKM(α)[M]    => "M"
  | SKM(α)[Ty #n] => s!"Type {n}"
  | SKM(α)[Prp]  => "Prop"
  | SKM(α)[⤳]  => "⤳"
  | SKM(α)[<~]  => "<~"
  | SKM(α)[→]  => "→"
  | SKM(α)[←]  => "←"
  | SKM(α)[t_in ⤳ t_out] => s!"({t_in.toStringImpl} ⤳ {t_out.toStringImpl})"
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
  | SKM(α)[(_t_in ⤳ t_out)] => t_out
  | e => e

end Expr

end Ast
