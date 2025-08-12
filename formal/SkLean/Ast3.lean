/-
# Judgment Rules & Ast: SK(M) Calculus

By adding just one combinator \\(M\\) to the SK calculus, dependent typing is achieved.

## The \\(M\\) Combinator: Evaluation Rules

\\(M\\) serves two purposes:

- Type-checking a program
- Type inference

As an example, the type of \\(K\ S\ K\\) should obviously be the type of \\(S\\), as \\(K\ S\ K = S\\).
Ideally, we can use \\(M\\) like such:

$$
M\ (e : t) = t \\\\
M\ (e : t)\ t_{2} = (t = t_{2})
$$

To facilitate this feature, I interpret the \\(K\\) combinator as an explicitly dependently-typed function of the form:

$$
K : \forall\ \alpha\ x\ y\ (h : M\ x\ \alpha), h\ \alpha\ \text{False}
$$

I interpret expressions of the type \\(M\ x\ \alpha\\) as decidable Church booleans. Here, \\(M\ x\ \alpha\\) acts like a proposition, as described above.

From here on, \\(K\\) refers to this explicitly-typed variant of \\(K\\).

## Decidability / Extracting a Truth Value from \\(M\\)

I aim for \\(M\\) to be total and terminating on all inputs. It is not clear how \\(M\\) can be interpreted to "type-check" a program, since it is total. By interpreting \\\(M\ e\ t\\) as a computable Church boolean, this can be easily achieved by indicating \\(\text{False}\\) or \\(\text{True}\\). Church booleans are implemented with polymphoric \\(K_{0}\\) and \\(S_{0}\\), which behave similarly to \\(\text{sorry}\\) in Lean.

```lean
-- Pseudo-code
def True  := K
def False := K (S K K)
```

It is not immediately clear what the types of the polymorphic \\(K\\) and \\(S\\) are.
I hard-code these types as \\(\text{Prop}\\):

$$
S_{0} : \text{Prop} \\\\
K_{0} : \text{Prop}
$$

Thus, the types of \\(False\\) and \\(True\\) are also \\(\text{Prop}\\).
-/

import Mathlib.Tactic

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | k₀   : Expr
  | s₀   : Expr
  | m₀   : Expr
  | prp  : Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat skmexpr
syntax "K"                                                             : skmexpr
syntax "S"                                                             : skmexpr
syntax "M"                                                             : skmexpr
syntax "Prop"                                                             : skmexpr
syntax "K₀"                                                             : skmexpr
syntax "S₀"                                                             : skmexpr
syntax "M₀"                                                             : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax ident                                                           : skmexpr
syntax "#" term                                                        : skmexpr
syntax "(" skmexpr ")"                                                 : skmexpr

syntax " ⟪ " skmexpr " ⟫ "                                             : term
syntax "SKM[ " skmexpr " ] "                                           : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K ⟫)                           => `(Expr.k)
  | `(⟪ S ⟫)                           => `(Expr.s)
  | `(⟪ M ⟫)                           => `(Expr.m)
  | `(⟪ K₀ ⟫)                          => `(Expr.k₀)
  | `(⟪ S₀ ⟫)                          => `(Expr.s₀)
  | `(⟪ M₀ ⟫)                          => `(Expr.m₀)
  | `(⟪ Prop ⟫)                        => `(Expr.prp)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)   => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

def Flse := SKM[(K₀ ((S₀ K₀) K₀))]
def Tre :=  SKM[(K₀)]

inductive is_eval_once : Expr → Expr → Prop
  | k      : is_eval_once SKM[((((K _t_x) x) _y) _h)] x
  | s      : is_eval_once SKM[(((((S _t) x) y) z) _h)] SKM[((x z) (y z))]
  | m_k₀   : is_eval_once SKM[(M K₀)] SKM[Prop]
  | m_s₀   : is_eval_once SKM[(M S₀)] SKM[Prop]

inductive is_eval_step : Expr → Expr → Prop
  | left : is_eval_step lhs lhs'
    → is_eval_step SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | step : is_eval_once e e'
    → is_eval_step e e'

inductive beta_eq : Expr → Expr → Prop
  | rfl   : beta_eq e e
  | eval  : is_eval_once e₁ e₂ → beta_eq e₁ e₂
  | left  : beta_eq lhs lhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right : beta_eq rhs rhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')]
  | trans : beta_eq e₁ e₂      → beta_eq e₂ e₃ → beta_eq e₁ e₃
  | symm  : beta_eq e₁ e₂      → beta_eq e₂ e₁

inductive is_normal_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e'))                 → is_normal_n 0 e e
  | succ  : is_eval_once e e' → is_normal_n n e' e_final → is_normal_n n.succ e e_final

def subtree_is_in (e in_e : Expr) : Prop :=
  e == in_e ∨
    match in_e with
      | SKM[(lhs rhs)] => subtree_is_in e lhs ∨ subtree_is_in e rhs
      | _ => false

inductive valid_judgment_hard : Expr → Expr → Prop
  | m : beta_eq SKM[(M e)] t
    → ¬ subtree_is_in e t
    → valid_judgment_hard e t

namespace valid_judgment_hard

lemma imp_m_eval : valid_judgment_hard e t → _root_.beta_eq SKM[(M e)] t :=
  fun h_t =>
    match h_t with
      | .m h_beq _ => h_beq

end valid_judgment_hard

lemma normal_beta_eq : is_normal_n n e e_final → beta_eq e e_final := by
  intro h
  induction h
  apply beta_eq.rfl
  case succ e e' n e_final h_eval h_norm h_eq =>
    apply beta_eq.symm
    apply beta_eq.trans
    exact beta_eq.symm h_eq
    apply beta_eq.symm
    exact beta_eq.eval h_eval

lemma m_stuck : is_normal_n 0 SKM[M] SKM[M] := by
  apply is_normal_n.stuck
  intro h
  cases h
  case a.intro h =>
    cases h

lemma k_stuck : is_normal_n 0 SKM[K] SKM[K] := by
  apply is_normal_n.stuck
  intro h
  cases h
  case a.intro h =>
    cases h

lemma s_stuck : is_normal_n 0 SKM[S] SKM[S] := by
  apply is_normal_n.stuck
  intro h
  cases h
  case a.intro h =>
    cases h

