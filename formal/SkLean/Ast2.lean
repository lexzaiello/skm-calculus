import Mathlib.Tactic

/-
# Hierarchied, Reflective SK

I want to make the SK combinators more expressive while maintaining simplicity. I also want to make a proof assistant based on them. In order to formalize properties of the combinators, we required a type system. We have seen thus far the typical typing of \\(K : \alpha \rightarrow \beta \rightarrow \alpha\\). I propose a binderless, expressive type system for the combinators featuring reflection.

## Type Constructors

The \\(K\\) and \\(S\\) combinators double as type constructors in my calculus. I define a mapping from the combinators to arrows:

$$
K : \alpha \rightarrow \beta \rightarrow \alpha
$$

For example, to construct the arrow \\(\alpha \rightarrow \alpha\\):

$$
SKS : \alpha \rightarrow \alpha
$$

- M is computable. It is not a type.
-/

inductive Expr where
  | m       : ℕ    → Expr
  | k       : ℕ    → Expr
  | s       : ℕ    → Expr
  | call    : Expr → Expr → Expr
  | ty      : Expr
deriving DecidableEq, Repr, BEq

namespace Expr

def sum_universes (e : Expr) : ℕ :=
  match e with
    | .m n => n
    | .k n => n
    | .s n => n
    | .call lhs rhs =>
      lhs.sum_universes + rhs.sum_universes

end Expr

/-
## DSL

We make use of a small DSL for legibility.
-/

declare_syntax_cat skmexpr
syntax "K" term                : skmexpr
syntax "S" term                : skmexpr
syntax "M" term                : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax ident                   : skmexpr
syntax "#" term                : skmexpr
syntax "(" skmexpr ")"         : skmexpr

syntax " ⟪ " skmexpr " ⟫ "     : term
syntax "SKM[ " skmexpr " ] "   : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K $e:term ⟫)                 => `(Expr.k $e)
  | `(⟪ S $e:term ⟫)                 => `(Expr.s $e)
  | `(⟪ M $e:term ⟫)                 => `(Expr.m $e)
  | `(⟪ $e:ident ⟫)                  => `($e)
  | `(⟪ # $e:term ⟫)                 => `($e)
  | `(⟪ ($e:skmexpr) ⟫)              => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫) => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

def implies (α β : Expr) : Expr :=
  let ty_β := SKM[((M β.sum_universes.succ) β)]
  SKM[((((K ty_β.sum_universes.succ) (ty_β)) α) β)]

inductive is_eval_once : Expr → Expr → Prop
  | k x y        : is_eval_once SKM[(((((K n) _α) _β) x) y)] x
  | s x y z      : is_eval_once SKM[(((((((S n) _α) _β) _γ) x) y) z)] SKM[((x z) (y z))]
  | m_k          : is_eval_once SKM[((M n.succ) (K n))] SKM[K n.succ]
  | m_s          : is_eval_once SKM[((M n.succ) (S n))] SKM[S n.succ]
  | m_m          : is_eval_once SKM[((M n.succ) (M n))] SKM[M n.succ]
  | m_call       : is_eval_once SKM[((M n) (lhs rhs))]
    SKM[(((M lhs.sum_universes.succ) lhs) ((M rhs.sum_universes.succ) rhs))]

inductive step_eval : Expr → Expr → Prop
  | once  : is_eval_once e e' → step_eval e e'
  | left  : step_eval lhs lhs'
    → step_eval SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right : step_eval rhs rhs'
    → step_eval SKM[(lhs rhs)] SKM[(lhs rhs')]

inductive beta_eq : Expr → Expr → Prop
  | rfl   : beta_eq e e
  | eval  : step_eval e₁ e₂  → beta_eq e₁ e₂
  | left  : beta_eq lhs lhs' → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right : beta_eq rhs rhs' → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')]
  | trans : beta_eq e₁ e₂    → beta_eq e₂ e₃ → beta_eq e₁ e₃
  | symm  : beta_eq e₁ e₂    → beta_eq e₂ e₁

inductive valid_judgment : Expr → Expr → Prop
  | k                         : valid_judgment SKM[K n] SKM[K n.succ]
  | s                         : valid_judgment SKM[S n] SKM[S n.succ]
  | m                         : valid_judgment SKM[M n] SKM[M n.succ]
  | call_k                    : valid_judgment x α
    → valid_judgment y β
    → valid_judgment SKM[(((((K n) α) β) x) y)] α
  | call_s                    : valid_judgment x SKM[(((K n) α) β)]
    → valid_judgment y SKM[((((K n) β) α) x_in_val)]
    → valid_judgment z α
    → valid_judgment SKM[(((((((S n) α) β) γ) x) y) z)] γ

inductive is_normal_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e'))                 → is_normal_n 0 e e
  | succ  : is_eval_once e e' → is_normal_n n e' e_final → is_normal_n n.succ e e_final

namespace is_normal_n

lemma m_stuck : is_normal_n 0 SKM[M] SKM[M] := by
  apply is_normal_n.stuck
  intro h
  obtain ⟨e', h_eval⟩ := h
  cases h_eval

lemma k_stuck : is_normal_n 0 SKM[K] SKM[K] := by
  apply is_normal_n.stuck
  intro h
  obtain ⟨e', h_eval⟩ := h
  cases h_eval

lemma s_stuck : is_normal_n 0 SKM[S] SKM[S] := by
  apply is_normal_n.stuck
  intro h
  obtain ⟨e', h_eval⟩ := h
  cases h_eval

end is_normal_n

namespace beta_eq

@[simp]
lemma m_distributes : beta_eq SKM[(M (lhs rhs))] SKM[((M lhs) (M rhs))] := by
  apply beta_eq.eval
  apply step_eval.once
  apply is_eval_once.m_call

lemma funext : beta_eq e₁ e' → beta_eq e₂ e' → beta_eq e₁ e₂ := by
  intro h_beq₁ h_beq₂
  induction h_beq₁
  exact beta_eq.symm h_beq₂
  case eval h =>
    apply beta_eq.symm
    apply beta_eq.trans
    exact h_beq₂
    exact beta_eq.symm (beta_eq.eval h)
  case left =>
    apply beta_eq.trans
    apply beta_eq.left
    case a.a h _ =>
      exact h
    exact beta_eq.symm h_beq₂
  case right =>
    apply beta_eq.trans
    apply beta_eq.right
    case a.a h _ =>
      exact h
    exact beta_eq.symm h_beq₂
  case trans =>
    apply beta_eq.trans
    case a h _ _ _ =>
      exact h
    simp_all
  case symm =>
    apply beta_eq.symm
    apply beta_eq.trans
    exact h_beq₂
    case a.a h _ =>
      exact h

end beta_eq
