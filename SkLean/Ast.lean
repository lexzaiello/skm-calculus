/-
# AST

## SK Dependent Typing

I interpret the SK combinators as dependently typed functions of the form:

$$
K\ (\alpha : \text{Type}\ m)\ (\beta : \text{Type}\ n) : \alpha \rightarrow \beta \rightarrow \alpha \\\\
S\ (\alpha : \text{Type}\ m)\ (\beta : \text{Type}\ n)\ (\gamma : \text{Type}\ o) : (\alpha \rightarrow \beta \rightarrow \gamma) \rightarrow (\alpha \rightarrow \beta) \rightarrow \alpha \rightarrow \gamma
$$

where \\(K\ \mathbb{N}\ \mathbb{R}\\) produces a function of type \\(\mathbb{N} \rightarrow \mathbb{R} \rightarrow \mathbb{N}\\).

Borrowing from the calculus of constructions, the types of \\(K\\) and \\(S\\) are explicitly given by the \\(\forall\\) expression:

$$
K : (\forall \alpha : \text{Type}\ m, \beta : \text{Type}\ n, x : \alpha\ y : \beta . \alpha) \\\\
S : (\forall \alpha : \text{Type}\ m, \beta : \text{Type}\ n, \gamma : \text{Type}\ o, \\\\
x : (\forall x : \alpha, y : \beta, z : \gamma . \gamma), y : (\forall x : \alpha . \beta), z : \alpha . \gamma)
$$

Typing judgements on function application are derived from substitution on \\(\forall\\). For example, the type of \\(K\ \mathbb{N}\\) is derived from substitution of \\(\mathbb{N}\\) into the type of \\(K\\). That is, \\(\alpha\\) is replaced with \\(\mathbb{N}\\), and the type of the expression is said to be equal to the body of the \\(\forall\\) in which the value was substituted.

The \\(K\\) and \\(S\\) combinators can be encoded in AST form in Lean using De Bruijn indices like such:
-/

import Mathlib.Tactic

/-
A `BindId n` refers to the value of the variable binder in the nth-up \\(\forall\\) expression.
-/
structure BindId where
  toNat : ℕ
deriving BEq, Repr, DecidableEq

namespace BindId

def succ (id : BindId) : BindId := ⟨id.toNat.succ⟩

instance : LT BindId where
  lt (slf : BindId) (other : BindId) : Prop :=
    slf.toNat < other.toNat

instance : DecidableRel (@LT.lt BindId _) :=
  fun a b => inferInstanceAs (Decidable (a.toNat < b.toNat))

end BindId

/-
For example, the expression \\(\forall x : \alpha.x\\) can be rewritten using De Bruijn indices to \\(\forall \alpha.1\\).

An expression is one of: \\(K\\), \\(S\\), \\(\text{Prop}\\), \\(\text{Ty}\ n\\), \\((\forall e_{1}.e_{2})\\), \\(e_{1}\ e_{2}\\), or a variable \\(n\\).

For convenience and legibility, I create a separate definition of each expression:
-/

inductive K where
  | mk : K
deriving BEq, Repr

inductive S where
  | mk : S
deriving BEq, Repr

inductive Prp where
  | mk : Prp
deriving BEq, Repr

/-
Stratified type universes.
-/
inductive Ty where
  | mk : ℕ → Ty
deriving BEq, Repr

mutual

inductive Call where
  | mk : SkExpr → SkExpr → Call
deriving BEq, Repr

/-
Var uses a 1-indexed De Bruijn position.
-/

inductive Var where
  | mk : BindId → Var
deriving BEq, Repr

/-
\\(\forall\\) takes a type of its binder \\(x : t\\), and has a body containing \\(e\\).
-/
inductive Fall where
  | mk : SkExpr → SkExpr → Fall

inductive SkExpr where
  | k    : K    → SkExpr
  | s    : S    → SkExpr
  | prp  : Prp  → SkExpr
  | ty   : Ty   → SkExpr
  | fall : Fall → SkExpr
  | call : Call → SkExpr
  | var  : Var  → SkExpr
deriving BEq, Repr

end

/-
Some convenience accessor methods:
-/

namespace Ty

def n : Ty → ℕ
  | .mk n => n

end Ty

namespace Call

def lhs : Call → SkExpr
  | .mk lhs _ => lhs

def rhs : Call → SkExpr
  | .mk _ rhs => rhs

end Call

namespace SkExpr

/-
Whenever a value is substituted in to a \\(\forall\\) expression, all its free variables must be incremented by 1 in order to prevent shadowing from the new surrounding expression.
-/

def with_indices_plus (in_expr : SkExpr) (shift_by : BindId) : SkExpr :=
  match in_expr with
    | .fall (.mk bind_ty body) =>
      .fall (.mk (bind_ty.with_indices_plus shift_by.succ) (body.with_indices_plus shift_by.succ))
    | .var (.mk n) =>
      if n > shift_by then
        var (.mk ⟨n.toNat + shift_by.toNat⟩)
      else
        var (.mk n)
    | .call (.mk lhs rhs) =>
      call (.mk (lhs.with_indices_plus shift_by) (rhs.with_indices_plus shift_by))
    | x => x

end SkExpr

namespace Fall

def bind_ty : Fall → SkExpr
  | .mk bind_ty _ => bind_ty

def body : Fall → SkExpr
  | .mk _ body => body

def substitute (in_fall : Fall) (with_expr : SkExpr) : Fall :=
  let rec substitute_e (in_expr : SkExpr) (n : BindId) (with_expr : SkExpr) : SkExpr :=
    match in_expr with
      | .fall (.mk bind_ty body) =>
        .fall (.mk (substitute_e bind_ty n.succ with_expr) (substitute_e body n.succ with_expr))
      | .var (.mk n') => if n = n' then with_expr.with_indices_plus n else .var (.mk n')
      | x => x
    match in_fall with
      | .mk bind_ty body =>
        .mk (substitute_e bind_ty ⟨1⟩ with_expr) (substitute_e body ⟨1⟩ with_expr)

end Fall

/-
I give a few test cases of index shifting:
-/

example : (SkExpr.fall (.mk (.ty (.mk 0)) (.var (.mk ⟨2⟩)))).with_indices_plus ⟨1⟩ = (SkExpr.fall (.mk (.ty (.mk 0)) (.var (.mk ⟨2⟩)))) := by
  repeat unfold SkExpr.with_indices_plus
  simp
  unfold BindId.succ
  simp
  unfold LT.lt
  unfold BindId.instLT
  simp

example : ((Fall.mk (.ty (.mk 0)) (.var (.mk ⟨1⟩)))).substitute (.var (.mk ⟨2⟩)) = (Fall.mk (.ty (.mk 0)) (.var (.mk ⟨3⟩))) := by
  unfold Fall.substitute
  simp
  repeat unfold Fall.substitute.substitute_e
  simp
  repeat unfold SkExpr.with_indices_plus
  simp
  unfold LT.lt
  unfold BindId.instLT
  simp

example : (Fall.mk (.ty (.mk 0)) (.var (.mk ⟨1⟩))).substitute (.fall (.mk (.ty (.mk 0)) (.var (.mk ⟨4⟩)))) = (Fall.mk (.ty (.mk 0)) ((.fall (.mk (.ty (.mk 0)) (.var (.mk ⟨6⟩)))))) := by
  unfold Fall.substitute
  simp
  repeat unfold Fall.substitute.substitute_e
  simp
  repeat unfold SkExpr.with_indices_plus
  simp
  split
  simp
  repeat unfold BindId.succ
  simp
  contradiction

/-
One-step evaluation is only defined for \\(K\ \alpha\ \beta\ x\ y\\) and \\(S\ \alpha\ \beta\ \gamma\ x\ y\ z\\).
-/

namespace Call

def eval_once : Call → SkExpr
  | (.mk (.call (.mk (.call (.mk (.call (.mk (.call (.mk (.k .mk) _)) _)) _)) x)) _) => x
  | (.mk (.call (.mk (.call (.mk (.call (.mk (.call (.mk (.call (.mk (.s .mk)  _)) _)) _)) x)) y)) z) => .call (.mk (.call (.mk x z)) (.call (.mk y z)))
  | (.mk x y) => (.call (.mk x y))

end Call
