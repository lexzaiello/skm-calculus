import Mathlib.Tactic
import Lean
import Lean.Elab.Term

namespace Ast

abbrev Universe := ℕ

inductive Expr where
  | k    : Universe → Universe → Expr
  | s    : Universe → Universe → Universe → Expr
  | m    : Expr
  | pi   : Expr
  | pi'  : Expr
  | imp  : Expr
  | imp' : Expr
  | hole : Expr
  | ty   : Universe → Expr
  | prp  : Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr, Lean.ToExpr

def max_universe : Expr → Universe
  | .k _m n => max _m n
  | .s _m n o => max (max _m n) o
  | .ty n => n
  | .call lhs rhs => max (max_universe lhs) (max_universe rhs)
  | _ => 0

inductive ExprBox (e : Ast.Expr) where
  | mk : ExprBox e

declare_syntax_cat skmexpr
syntax "@" skmexpr                                     : skmexpr
syntax "K" skmexpr skmexpr                             : skmexpr
syntax "S" skmexpr skmexpr skmexpr                     : skmexpr
syntax "K" skmexpr skmexpr                             : skmexpr
syntax "S" skmexpr skmexpr skmexpr                     : skmexpr
syntax "K₀"                                            : skmexpr
syntax "K+" skmexpr skmexpr skmexpr*                   : skmexpr
syntax "(" "_" ":" skmexpr ")"                         : skmexpr
syntax "(" skmexpr ":" skmexpr ")"                     : skmexpr
syntax "λ" skmexpr skmexpr* "=>" skmexpr               : skmexpr
syntax "I" skmexpr                                     : skmexpr
syntax "S₀"                                            : skmexpr
syntax "M"                                             : skmexpr
syntax "~>"                                            : skmexpr
syntax "<~"                                            : skmexpr
syntax "→"                                             : skmexpr
syntax "←"                                             : skmexpr
syntax "always" skmexpr                                : skmexpr
syntax "Ty" term                                       : skmexpr
syntax "Prp"                                           : skmexpr
syntax "self" skmexpr                                  : skmexpr
syntax "?"                                             : skmexpr
syntax skmexpr "~>" skmexpr                            : skmexpr
syntax skmexpr "<~" skmexpr                            : skmexpr
syntax skmexpr "→" skmexpr                             : skmexpr
syntax skmexpr "←" skmexpr                             : skmexpr
syntax "codomain" skmexpr                              : skmexpr
syntax "domain" skmexpr                                : skmexpr
syntax "(" skmexpr skmexpr ")"                         : skmexpr
syntax "(" skmexpr skmexpr skmexpr* ")"                : skmexpr
syntax ident                                           : skmexpr
syntax "#" term                                        : skmexpr
syntax "(" skmexpr ")"                                 : skmexpr
syntax "∀" skmexpr skmexpr* "," skmexpr                : skmexpr

syntax "⟪" skmexpr "⟫"      : term
syntax "⟨⟪" skmexpr "⟫⟩"    : skmexpr
syntax "SKM[" skmexpr "]"   : term

macro_rules
  | `(SKM[ $e:skmexpr ])  => `(⟪ $e ⟫)

macro_rules
  | `(⟪ domain $t_in ~> $_t_out ⟫) => pure t_in
  | `(⟪ codomain $_t_in ~> $t_out ⟫) => pure t_out
  | `(⟪ ((@(→) $t₁ $t₂) : ?) ⟫) => `(SKM[(∀ (_ : $t₁) (_ : $t₂), Ty (max (max_universe m) (max_universe n)).succ)])
  | `(⟪ (K α β : ?) ⟫) => `(SKM[(K α β : ∀ (_ : α) (_ : β), α)])
  | `(⟪ (S ? ? ? ($x : $t_x)) ⟫) => `(SKM[(S (codomain (codomain $t_x)) (domain (codomain $t_x)) (domain $t_x) $x)])
  | `(⟪ ($e₁ $e₂ $rest*) ⟫) => match rest.toList with
    | x :: xs => `(SKM[(($e₁ $e₂) $x $(⟨xs⟩)*)])
    | _ => `(SKM[($e₁ $e₂)])
  | `(⟪ (_ : $t:skmexpr )⟫) => `(SKM[$t])
  | `(⟪ α ~> always $t:skmexpr ⟫)          => `(SKM[α ~> (K ? α $t)])
  | `(⟪ @K #$m #$n ⟫) => `(Expr.k $m $n)
  | `(⟪ @S #$m #$n #$o ⟫) => `(Expr.s $m $n $o)
  | `(⟪ K $m:skmexpr $n:skmexpr ⟫)       => `(SKM[(((@K #(max_universe ⟪$m⟫) #(max_universe ⟪$n⟫)) $m) $n)])
  | `(⟪ (K ? $t_y:skmexpr ($e : $et)) ⟫) => `(SKM[((K $et $t_y) $e)])
  | `(⟪ (K ? $t_y:skmexpr $e) ⟫)         => `(SKM[((K (M $e) $t_y) $e)])
  | `(⟪ K+ $t:skmexpr $x:skmexpr $tys:skmexpr* ⟫) =>
    match tys.toList with
    | next :: xs =>
      let tys' := Array.mk xs.reverse
      `(SKM[((K+ (M (K $t $x)) $next $tys'*) (K $t $x))])
    | _ => `(SKM[(K $t $x)])
  | `(⟪ (K+ ? $x:skmexpr $tys:skmexpr* $e:skmexpr) ⟫) => `(SKM[((K+ (M $e) $x $tys*) $e)])
  | `(⟪ S $m:skmexpr $n:skmexpr $o:skmexpr ⟫) => `(SKM[((((@S #(max_universe ⟪$m⟫) #(max_universe ⟪$n⟫) #(max_universe ⟪$o⟫)) $m) $n) $o)])
  | `(⟪ M ⟫)                            => `(Expr.m)
  | `(⟪ ? ⟫)                            => `(Expr.hole)
  | `(⟪ Ty $n:term ⟫)                   => `(Expr.ty $n)
  | `(⟪ Prp ⟫)                          => `(Expr.prp)
  | `(⟪ ~> ⟫)                           => `(Expr.pi)
  | `(⟪ <~ ⟫)                           => `(Expr.pi')
  | `(⟪ → ⟫)                            => `(Expr.imp)
  | `(⟪ ← ⟫)                            => `(Expr.imp')
  | `(⟪ $e₁:skmexpr ~> $e₂:skmexpr ⟫)   => `(SKM[(((~>) $e₁) $e₂)])
  | `(⟪ $e₁:skmexpr <~ $e₂:skmexpr ⟫)   => `(SKM[($e₂ ~> $e₁)])
  | `(⟪ $e₁:skmexpr → $e₂:skmexpr ⟫)    => `(SKM[∀ (_ : $e₁), $e₂])
  | `(⟪ $e₁:skmexpr ← $e₂:skmexpr ⟫)    => `(SKM[$e₂ → $e₁])
  | `(⟪ $e:ident ⟫)                     => `($e)
  | `(⟪ # $e:term ⟫)                    => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                 => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)    => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)
  -- Accepts an expression of type e, returning type e
  | `(⟪ self $e:skmexpr ⟫)              => `(SKM[(K (M $e) $e $e)])
  | `(⟪ λ (_ : $t:skmexpr) $tys:skmexpr* => $body:skmexpr ⟫) => `(SKM[((K+ (M $body) $t $tys*) $body)])
  | `(⟪ ∀ (x : $t:skmexpr), x ⟫) => `(SKM[(~> self $t)])
  | `(⟪ ∀ (x : $t:skmexpr), (f x) ⟫) => `(SKM[self $t ~> f])
  | `(⟪ ∀ (_ : $t:skmexpr) $tys:skmexpr*, $body:skmexpr ⟫) => do
    let tys := [t] ++ tys.toList.filterMap (λ stx =>
      match stx with
      | `(skmexpr| (_ : $t)) => pure t
      | _ => none)

    let e_body ← (`(skmexpr| ((K+ (M $body) $t $(⟨tys⟩)*) $body)))

    `(⟪$((← (tys.foldrM (λ t_out (e, rem) => do match rem.reverse with
      | t :: xs => pure (← (`(skmexpr| ((λ (_:$t) $(⟨← xs.mapM (λ e => `(skmexpr| (_:$e)))⟩)* => $t_out) ~> $e))), xs)
      | _ => pure (← (`(skmexpr| K+ ? $t $(⟨tys⟩)* body)), [])) (e_body, tys))).fst)⟫)

namespace Expr

def toStringImpl (e : Expr) : String :=
  match e with
  | SKM[@S #_m #n #o]  => s!"S.{_m},{n},{o}"
  | SKM[@K #_m #n]    => s!"K.{_m},{n}"
  | SKM[M]    => "M"
  | SKM[Ty n] => s!"Type {n}"
  | SKM[Prp]  => "Prop"
  | SKM[?]    => "?"
  | SKM[~>]  => "~>"
  | SKM[<~]  => "<~"
  | SKM[→]  => "→"
  | SKM[←]  => "←"
  | SKM[(t_in ~> t_out)] => s!"({t_in.toStringImpl} ~> {t_out.toStringImpl})"
  | SKM[(lhs rhs)] => s!"({lhs.toStringImpl} {rhs.toStringImpl})"

instance : ToString Expr where
  toString := toStringImpl

#eval SKM[λ (_ : Ty 1) (_ : Ty 2) => M]
#eval SKM[∀ (_ : Ty 1) (_ : Ty 2), M]

def insert_arrow_arg (in_e e : Ast.Expr) : Ast.Expr :=
  match in_e with
  | SKM[(t_in ~> t_out)] =>
    SKM[(#(insert_arrow_arg t_in e) ~> #(insert_arrow_arg t_out e))]
  | x => SKM[(x e)]

def pop_arrow : Ast.Expr → Ast.Expr
  | SKM[(_t_in ~> t_out)] => t_out
  | e => e

end Expr

def mk_k_type_eta (α β : Expr) : Expr :=
  let inner_k := SKM[((K ? (M β)) α)]

  SKM[(α ~> (β ~> ((K ? α) inner_k)))]

syntax "I" skmexpr : skmexpr

def i (t : Expr) : Expr :=
  let t_k_right := mk_k_type_eta t t

  let k_right := SKM[(K t t)]
  let k_left := SKM[(K t t_k_right)]

  SKM[(((S t (t → t) t) k_left) k_right)]

macro_rules
  | `(⟪ I $t:skmexpr ⟫) => `(SKM[#(i ⟪$t⟫)])


def mk_k_type (_m n : Universe) : Ast.Expr :=
  SKM[Ty _m ~> Ty n ~> (((((K _m n) Ty _m) Ty n) (~>)) (<~))]

namespace Expr

def fromExpr (e : Lean.Expr) : Option Expr :=
  match e with
  | .const `Expr.hole [] => pure SKM[?]
  | (.app
      (.app (.const `Expr.k []) (.lit (.natVal _m)))
      (.lit (.natVal n)))    => pure SKM[K _m n]
  | (.app
      (.app
        (.app (.const `Expr.s []) (.lit (.natVal _m)))
        (.lit (.natVal n))) (.lit (.natVal o)))    => pure SKM[S _m n o]
  | .const `Expr.m []    => pure SKM[M]
  | .const `Expr.pi [] => pure SKM[~>]
  | .const `Expr.pi' [] => pure SKM[<~]
  | .const `Expr.imp [] => pure SKM[→]
  | .const `Expr.imp' [] => pure SKM[←]
  | .sort .zero => pure SKM[Prp]
  | .sort n => pure SKM[Ty n.depth.pred]
  | .app (.app (.const `Expr.call []) lhs) rhs => do
    let lhs' ← fromExpr lhs
    let rhs' ← fromExpr rhs
    pure SKM[(lhs' rhs')]
  | _ => none

/-
K type with dependent arrow:

K α : (K α) ~> (~> α)
K : S (K ~>) (S K ~>)
-/

end Expr

end Ast
