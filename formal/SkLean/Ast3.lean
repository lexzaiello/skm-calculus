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
  | hole : Expr
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
syntax "@" skmexpr                                     : skmexpr
syntax "K₀"                                            : skmexpr
syntax "K+"                                            : skmexpr
syntax "K"                                             : skmexpr
syntax "S"                                             : skmexpr
syntax skmexpr ":" skmexpr                             : skmexpr
syntax "λ" skmexpr skmexpr* "=>" skmexpr               : skmexpr
syntax "I" skmexpr                                     : skmexpr
syntax "S₀"                                            : skmexpr
syntax "M"                                             : skmexpr
syntax "~>"                                            : skmexpr
syntax "<~"                                            : skmexpr
syntax "→"                                             : skmexpr
syntax "←"                                             : skmexpr
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
syntax "(" skmexpr skmexpr skmexpr* ")"                : skmexpr
syntax ident                                           : skmexpr
syntax "#" term                                        : skmexpr
syntax "(" skmexpr ")"                                 : skmexpr
syntax "∀" skmexpr skmexpr* "," skmexpr                : skmexpr

syntax "(" term ")" "⟪" skmexpr "⟫"         : term
syntax "SKM" "(" term ")" "[" skmexpr "]"   : term

macro_rules
  | `(SKM ($t:term) [ $e:skmexpr ])  => `((($t) ⟪ $e ⟫ : (@Expr $t)))

macro_rules
  | `(($t_inner:term)⟪ (M ($_e:skmexpr : $t:skmexpr)) ⟫) => pure t
  | `(($t_inner:term)⟪ domain $t_in:skmexpr ~> $_t_out:skmexpr ⟫) => pure t_in
  | `(($t_inner:term)⟪ codomain $_t_in:skmexpr ~> $t_out:skmexpr ⟫) => pure t_out
  | `(($t_inner:term)⟪ (M (@(→) $t₁:skmexpr $t₂:skmexpr)) ⟫) => `(SKM($t_inner)[(∀ (x : $t₁) (y : $t₂), Ty (max (($t_inner)⟪$t₁⟫.max_universe) (($t_inner)⟪$t₂⟫.max_universe)).succ)])
  | `(($t_inner:term)⟪ (M ((K $α:skmexpr $β:skmexpr))) ⟫) => `(SKM($t_inner)[(K $α $β) : ∀ (x : $α) (y : $β), $α])
  | `(($t_inner:term)⟪ (M ($f:skmexpr $arg:skmexpr)) ⟫) => `(SKM($t_inner)[((M $f) $arg)])
  | `(($t_inner:term)⟪ (S ? ? $t_z:skmexpr $x:skmexpr) ⟫) => do
    let t_x ← `(skmexpr| (M $x))
    `(SKM($t_inner)[(S (codomain (codomain $t_x)) (domain (codomain $t_x)) $t_z $x)])
  | `(($t_inner:term)⟪ (@S #$m:term #$n:term #$o:term) ⟫) => `(@Expr.s $t_inner $m $n $o)
  | `(($t_inner:term)⟪ (@K #$m:term #$n:term) ⟫) => `(@Expr.k $t_inner $m $n)
  | `(($t_inner:term)⟪ (S $m:skmexpr $n:skmexpr $o:skmexpr) ⟫) => `(SKM($t_inner)[((((@S #(($t_inner)⟪$m⟫.max_universe) #(($t_inner)⟪$n⟫.max_universe) #(@($t_inner)⟪$o⟫.max_universe _)) $m) $n) $o)])
  | `(($t_inner:term)⟪ (K ? $t_y:skmexpr ($e : $et)) ⟫) => `(SKM($t_inner)[((K $et $t_y) $e)])
  | `(($t_inner:term)⟪ (K $m:skmexpr $n:skmexpr) ⟫) => `(SKM($t_inner)[(((@K #(@($t_inner)⟪$m⟫.max_universe _) #(@($t_inner)⟪$n⟫.max_universe _)) $m) $n)])
  | `(($t_inner:term)⟪ (K ? $t_y:skmexpr $e) ⟫) => `(SKM($t_inner)[((K (M $e) $t_y) $e)])
  | `(($t_inner:term)⟪ ((K+ ? $x:skmexpr $tys:skmexpr*) $e:skmexpr) ⟫) => `(SKM($t_inner)[((K+ (M $e) $x $tys*) $e)])
  | `(($t_inner:term)⟪ (K+ $t:skmexpr $x:skmexpr $tys:skmexpr*) ⟫) =>
    match tys.toList with
    | next :: xs =>
      let tys' := Array.mk xs.reverse
      `(SKM($t_inner)[((K+ (M (K $t $x)) $next $tys'*) (K $t $x))])
    | _ => `(SKM($t_inner)[(K $t $x)])
  | `(($t_inner:term)⟪ M ⟫)                            => `(@Expr.m $t_inner)
  | `(($t_inner:term)⟪ ? ⟫)                            => `(@Expr.hole $t_inner)
  | `(($t_inner:term)⟪ Ty $n:term ⟫)                   => `(@Expr.ty $t_inner $n)
  | `(($t_inner:term)⟪ Prp ⟫)                          => `(@Expr.prp $t_inner)
  | `(($t_inner:term)⟪ ~> ⟫)                           => `(@Expr.pi $t_inner)
  | `(($t_inner:term)⟪ <~ ⟫)                           => `(@Expr.pi' $t_inner)
  | `(($t_inner:term)⟪ → ⟫)                            => `(@Expr.imp $t_inner)
  | `(($t_inner:term)⟪ ← ⟫)                            => `(@Expr.imp' $t_inner)
  | `(($t_inner:term)⟪ $e₁:skmexpr ~> $e₂:skmexpr ⟫)   => `(SKM($t_inner)[(((~>) $e₁) $e₂)])
  | `(($t_inner:term)⟪ $e₁:skmexpr <~ $e₂:skmexpr ⟫)   => `(SKM($t_inner)[($e₂ ~> $e₁)])
  | `(($t_inner:term)⟪ $e₁:skmexpr → $e₂:skmexpr ⟫)    => `(SKM($t_inner)[∀ (x : $e₁), $e₂])
  | `(($t_inner:term)⟪ $e₁:skmexpr ← $e₂:skmexpr ⟫)    => `(SKM($t_inner)[$e₂ → $e₁])
  | `(($t_inner:term)⟪ $e:ident ⟫)                     => `($e)
  | `(($t_inner:term)⟪ # $e:term ⟫)                    => `($e)
  | `(($t_inner:term)⟪ ($e:skmexpr) ⟫)                 => `(($t_inner)⟪$e⟫)
  -- Accepts an expression of type e, returning type e
  | `(($t_inner:term)⟪ self $e:skmexpr ⟫)              => `(SKM($t_inner)[(K (M $e) $e $e)])
  | `(($t_inner:term)⟪ λ ($_v:skmexpr : $t:skmexpr) => ($e₁:skmexpr $e₂:skmexpr) ⟫) =>
    `(SKM($t_inner)[(S ? ? $t $e₁ $e₂)])
  | `(($t_inner:term)⟪ λ ($_v:skmexpr : $t:skmexpr) => $body:skmexpr ⟫) => `(SKM($t_inner)[(K ? $t $body)])
  | `(($t_inner:term)⟪ λ ($_v : $t:skmexpr) $tys:skmexpr* => $body:skmexpr ⟫) =>
    match tys.toList with
    | stx::xs => `(SKM($t_inner)[λ ($_v : $t) => (λ $stx $(⟨xs⟩)* => $body)])
    | _ => `(SKM($t_inner)[λ ($_v : $t) => $body])
  | `(($t_inner:term)⟪ ($e₁:skmexpr $e₂:skmexpr $rest:skmexpr*) ⟫) => match rest.toList with
    | x :: xs => `(SKM($t_inner)[(($e₁ $e₂) $x $(⟨xs⟩)*)])
    | _ => `(@Expr.call $t_inner ($t_inner)⟪$e₁⟫ ($t_inner)⟪$e₂⟫)
  | `(($t_inner:term)⟪ ∀ ($x:ident : $t:skmexpr), ($f:skmexpr $x:ident) ⟫) => `(SKM($t_inner)[self $t ~> $f])
  | `(($t_inner:term)⟪ ∀ ($x:skmexpr : $t:skmexpr), $x:skmexpr ⟫) =>`(SKM($t_inner)[(~> self $t)])
  | `(($t_inner:term)⟪ ∀ ($_:skmexpr : $t:skmexpr) $tys:skmexpr*, $body:skmexpr ⟫) => do
    let tys := [t] ++ tys.toList.filterMap (λ stx =>
      match stx with
      | `(skmexpr| ($_:skmexpr : $t:skmexpr)) => pure t
      | _ => none)

    let e_body ← (`(skmexpr| ((K+ (M $body) $t $(⟨tys⟩)*) $body)))

    pure $ (((← (tys.foldrM (λ t_out ((e, rem) : (Lean.TSyntax `skmexpr) × (List $ Lean.TSyntax `skmexpr)) => do match rem.reverse with
      | t :: xs =>
        let tys' ← xs.mapM (λ e => `(skmexpr| (_v:$e)))
        pure (← (`(skmexpr| ((λ (_v:$t) $(⟨tys'⟩)* => $t_out) ~> $e))), xs)
      | _ => pure (← (`(skmexpr| ((K+ ? $t $(⟨tys⟩)*) body))), [])) (e_body, tys))).fst))

namespace Expr

#eval SKM (Unit) [(λ (x : Ty 0) => ((K Ty 0  Ty 0) (K Ty 0 Ty 0)))]

def toStringImpl [ToString α] (e : @Expr α) : String :=
  match e with
  | SKM(α)[(@S #_m #n #o)]  => s!"S.{_m},{n},{o}"
  | SKM(α)[(@K #_m #n)]    => s!"K.{_m},{n}"
  | SKM(α)[M]    => "M"
  | SKM(α)[Ty n] => s!"Type {n}"
  | SKM(α)[Prp]  => "Prop"
  | SKM(α)[?]    => "?"
  | SKM(α)[~>]  => "~>"
  | SKM(α)[<~]  => "<~"
  | SKM(α)[→]  => "→"
  | SKM(α)[←]  => "←"
  | SKM(α)[(t_in ~> t_out)] => s!"({t_in.toStringImpl} ~> {t_out.toStringImpl})"
  | SKM(α)[(lhs rhs)] => s!"({lhs.toStringImpl} {rhs.toStringImpl})"
  | .cnst c => s!"{c}"

instance {α : Type} [ToString α] : ToString (@Expr α) where
  toString := toStringImpl

#eval SKM (Unit) [λ (_v : Ty 1) (_u : Ty 2) => M]

def insert_arrow_arg {α : Type} (in_e e : @Ast.Expr α) : @Ast.Expr α :=
  match in_e with
  | SKM(α)[(t_in ~> t_out)] =>
    SKM(α)[(#(insert_arrow_arg t_in e) ~> #(insert_arrow_arg t_out e))]
  | x => SKM(α)[(x e)]

def pop_arrow {α : Type} : @Ast.Expr α → @Ast.Expr α
  | SKM(_)[(_t_in ~> t_out)] => t_out
  | e => e

end Expr

def mk_k_type {α : Type} (_m n : Universe) : @Ast.Expr α :=
  sorry

end Ast
