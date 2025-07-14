import Mathlib.Tactic

inductive LExpr where
  | var   : ℕ     → LExpr
  | app   : LExpr → LExpr → LExpr
  | lam   : LExpr → LExpr
  | m     : LExpr
  | s     : LExpr
  | k     : LExpr
  | const : String → LExpr
  | hole  : LExpr

inductive SkExpr where
  | s     : ℕ      → SkExpr
  | k     : ℕ      → SkExpr
  | m     : ℕ      → SkExpr
  | call  : SkExpr → SkExpr → SkExpr
  | hole  : SkExpr
  | const : String → SkExpr
  | lam   : SkExpr → SkExpr
  | var   : ℕ      → SkExpr
deriving BEq, Nonempty

declare_syntax_cat skmexpr
syntax "K" term                : skmexpr
syntax "S" term                : skmexpr
syntax "M" term                : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax "?"                     : skmexpr
syntax ident                   : skmexpr
syntax "#" term                : skmexpr
syntax "λ" skmexpr             : skmexpr
syntax "(" skmexpr ")"         : skmexpr

syntax " ⟪ " skmexpr " ⟫ "     : term
syntax "SKM[ " skmexpr " ] "   : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K $e:term ⟫)                 => `(SkExpr.k $e)
  | `(⟪ S $e:term ⟫)                 => `(SkExpr.s $e)
  | `(⟪ M $e:term ⟫)                 => `(SkExpr.m $e)
  | `(⟪ ? ⟫)                         => `(SkExpr.hole)
  | `(⟪ $e:ident ⟫)                  => `($e)
  | `(⟪ # $e:term ⟫)                 => `($e)
  | `(⟪ ($e:skmexpr) ⟫)              => `(⟪$e⟫)
  | `(⟪ λ $e:skmexpr ⟫)              => `(SkExpr.lam ⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫) => `(SkExpr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

namespace SkExpr

def toStringImpl : SkExpr → String
    | .s n          => s!"S {n}"
    | .k n          => s!"K {n}"
    | .m n          => s!"M {n}"
    | .call lhs rhs => s!"({lhs.toStringImpl} {rhs.toStringImpl})"
    | .const str    => s!"{str}"
    | .hole         => "_"
    | .lam body     => s!"λ {body.toStringImpl}"
    | .var v        => s!"var {v}"

instance : ToString SkExpr where
  toString := SkExpr.toStringImpl

def sum_universes : SkExpr → ℕ
  | SKM[(K n)]       => n
  | SKM[(S n)]       => n
  | SKM[(M n)]       => n
  | SKM[?]           => 0
  | SKM[(lhs rhs)]   => lhs.sum_universes + rhs.sum_universes
  | SKM[λ body]      => body.sum_universes
  | x => 0

def fill_universes : SkExpr → SkExpr
  | SKM[((K _n) rhs)] => SKM[((K rhs.sum_universes) rhs)]
  | SKM[((S _n) rhs)] => SKM[((S rhs.sum_universes) rhs)]
  | SKM[((M _n) rhs)] => SKM[((M rhs.sum_universes) rhs)]
  | x => x

partial def eval_n (n : ℕ) (e : SkExpr) : SkExpr :=
  if n = 0 then
    e
  else
    let e' := match e with
      | SKM[(((((K _n) _α) _β) x) _y)] => x
      | SKM[(((((((S _n) _α) _β) _γ) x) y) z)] => eval_n n.pred SKM[((x z) (y z))]
      | SKM[(lhs rhs)] => eval_n n.pred.pred SKM[((#(eval_n n.pred lhs)) (#(eval_n n.pred rhs)))] 
      | x => x

      eval_n  n.pred.pred.pred e'

end SkExpr

partial def normalize' (e : SkExpr) : SkExpr :=
  match e with
    | .lam (.var 0) => SKM[((((((S 0) ?) ?) ?) (((K 0) ?) ?)) (((K 0) ?) ?))]
    | .lam (.var $ n + 1) => SKM[((((K 0) ?) ?) #(.var n))]
    | .k n => SKM[(K n)]
    | .m n => SKM[(M n)]
    | .s n => SKM[(S n)]
    | .lam (.call lhs rhs) => normalize' SKM[((((((S 0) ?) ?) ?) #(normalize' (.lam lhs))) #(normalize' (.lam rhs)))]
    | .lam x => SKM[((((K 0) ?) ?) #(normalize' x))]
    | .const c => .const c
    | .call lhs rhs => SKM[(#(normalize' lhs) #(normalize' rhs))]
    | .var n       => .var n
    | .hole => .hole

partial def to_sk (e : LExpr) : SkExpr :=
  match e with
    | .lam (.var 0) => SKM[((((((S 0) ?) ?) ?) (((K 0) ?) ?)) (((K 0) ?) ?))]
    | .lam (.var $ n + 1) => normalize' (.lam SKM[((((K 0) ?) ?) #(.var n))])
    | .k => SKM[K 0]
    | .m => SKM[M 0]
    | .s => SKM[S 0]
    | (.app lhs rhs) => normalize' SKM[((#(to_sk lhs)) #(to_sk rhs))]
    | .lam (.app lhs rhs) => normalize' SKM[(((((((S 0) ?) ?) ?) #(.lam $ to_sk lhs))) #(.lam $ to_sk rhs))]
    | .lam x => normalize' (.lam SKM[#(normalize' ∘ to_sk $ x)])
    | .const c => .const c
    | .var 0       => .var 0
    | .var v       => .var v
    | .hole        => .hole

#eval (LExpr.app ((LExpr.app (.lam (.lam (.app (.app (.app .k (.app .m (.var 0))) (.var 1)) (.var 0))))) (.const "α"))) (.const "β")
  |> SkExpr.eval_n 20 ∘ normalize' ∘ to_sk
