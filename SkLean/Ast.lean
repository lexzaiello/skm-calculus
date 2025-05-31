/-
# Dependently-Typed SK Combinators

I interpret the SK combinators as dependently typed functions of the form:

$$
K\ (\alpha : \text{Type}\ m)\ (\beta : \text{Type}\ n) : \alpha \rightarrow \beta \rightarrow \alpha \\\\
S\ (\alpha : \text{Type}\ m)\ (\beta : \text{Type}\ n)\ (\gamma : \text{Type}\ o) : (\alpha \rightarrow \beta \rightarrow \gamma) \rightarrow (\alpha \rightarrow \beta) \rightarrow \alpha \rightarrow \gamma
$$

where \\(K\ \mathbb{N}\ \mathbb{R}\\) produces a function of type \\(\mathbb{N} \rightarrow \mathbb{R} \rightarrow \mathbb{N}\\).

Borrowing from the calculus of constructions, the types of \\(K\\) and \\(S\\) are explicitly given by the \\(\forall\\) expression:

$$
K : (\forall \alpha : \text{Type}\ m, \beta : \text{Type}\ n, x : \alpha\ y : \beta . \alpha) \\\\
S : (\forall \alpha : \text{Type}\ m, \beta : \text{Type}\ n, \gamma : \text{Type}\ o, x : (\forall x : \alpha, y : \beta, z : \gamma . \gamma), y : (\forall x : \alpha, y : \beta . \alpha), z : \alpha . \gamma)
$$

Typing judgements on function application are derived from substitution on \\(\forall\\). For example, the type of \\(K\ \mathbb{N}\\) is derived from substitution of \\(\mathbb{N}\\) into the type of \\(K\\). That is, \\(\alpha\\) is replaced with \\(\mathbb{N}\\), and the type of the expression is said to be equal to the body of the \\(\forall\\) in which the value was substituted.

The K and S combinators can be encoded in AST form in Lean using De Bruijn indices like such:
-/

import Mathlib.Data.Nat.Notation

/-
A `BindId n` refers to the value of the variable binder in the nth-up \\(\forall\\) expression.
-/
structure BindId where
  toNat : ℕ
deriving BEq, Repr

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
-/

inductive SkExpr where
  | k    : SkExpr
  | s    : SkExpr
  | prp  : SkExpr
  | ty   : ℕ      → SkExpr
  | fall : SkExpr → SkExpr → SkExpr
  | call : SkExpr → SkExpr → SkExpr
  | var  : BindId → SkExpr
deriving BEq, Repr

namespace SkExpr

/-
Whenever a value is substituted in to a \\(\forall\\) expression, all its free variables must be incremented by 1 in order to prevent shadowing from the new surrounding expression.
-/

def with_indices_plus (in_expr : SkExpr) (shift_by : BindId) : SkExpr :=
  match in_expr with
    | fall bind_ty body =>
      fall (bind_ty.with_indices_plus shift_by.succ) (body.with_indices_plus shift_by.succ)
    | var n =>
      if n > shift_by then
        var ⟨n.toNat + shift_by.toNat⟩
      else
        var n
    | call lhs rhs =>
      call (lhs.with_indices_plus shift_by) (rhs.with_indices_plus shift_by)
    | x => x

def substitute (in_expr : SkExpr) (n : BindId) (with_expr : SkExpr) : SkExpr :=
  match in_expr with
    | fall bind_ty body =>
      fall (bind_ty.substitute n.succ with_expr) (body.substitute n.succ with_expr)
    | var n' => if n == n' then with_expr.with_indices_plus n else var n'
    | x => x

/-
I give a few test cases of index shifting:
-/

example : (fall (ty 0) (var ⟨2⟩)).with_indices_plus ⟨1⟩ = (fall (ty 0) (var ⟨2⟩)) := by
  repeat unfold with_indices_plus
  simp
  intro h
  unfold BindId.succ
  simp
  contradiction

example : (fall (ty 0) (var ⟨1⟩)).substitute ⟨0⟩ (var ⟨2⟩) = (fall (ty 0) (var ⟨3⟩)) := by
  unfold substitute
  simp
  repeat unfold substitute
  simp
  split
  repeat unfold with_indices_plus
  simp
  split
  simp
  unfold BindId.succ
  simp
  contradiction
  simp_all
  repeat unfold BindId.succ at *
  simp_all
  contradiction

example : (fall (ty 0) (var ⟨1⟩)).substitute ⟨0⟩ (fall (ty 0) (var ⟨4⟩)) = (fall (ty 0) ((fall (ty 0) (var ⟨6⟩)))) := by
  unfold substitute
  simp
  repeat unfold substitute
  simp
  split
  case isTrue h =>
    repeat unfold with_indices_plus
    simp
    repeat unfold BindId.succ at *
    simp_all
    unfold LT.lt
    unfold BindId.instLT
    simp
  case isFalse h =>
    simp_all
    contradiction

/-
When inferring the type of a function application, the rhs of the application is substituted in to the left hand side's type (\\(\forall\\)). The type of the application is said to be equivalent to the body of the substituted \\(\forall\\). See [type inference rules](./Typing.lean.md) for more.
-/

def body : SkExpr → Option SkExpr
  | fall _ body => some body
  | _ => none

/-
One-step evaluation is only defined for \\(K\ \alpha\ \beta\ x\ y\\) and \\(S\ \alpha\ \beta\ \gamma\ x\ y\ z\\).
-/

def eval_once : SkExpr → SkExpr
  | (call (call (call (call k _) _) x) _) => x
  | call (call (call (call (call (call s _) _) _) x) y) z => call (call x z) (call y z)
  | x => x

end SkExpr
