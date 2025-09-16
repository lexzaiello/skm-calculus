import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Checker.TypeDefs
import SkLean.Error

open Ast
open Ast.Expr

namespace Expr

def eval_step : Expr → Option Expr
  | ⟪ K (#_α) (#_β) (#x) (#y) ⟫ => pure x
  | ⟪ S (#_α) (#_β) (#_γ) (#x) (#y) (#z) ⟫ => pure ⟪ (#x) (#z) ((#y) (#z)) ⟫
  | ⟪ M K (T (#α)) (T (#β)) ⟫ => pure ⟪ (#α) → (#β) → (#α) ⟫
  | ⟪ M S (#α) ⟫ => pure ⟪ ((#α) → Type) → ((#α) → Type) → (T Syntax) ⟫
  | ⟪ ((#_t_in) → (#t_out)) (#arg) ⟫ => t_out
  | ⟪ (#lhs) (#rhs) ⟫ => do
    ⟪ (#← eval_step lhs) (#rhs) ⟫
  | _ => .none

partial def eval_unsafe (e : Expr) : Option Expr := do
  let e' := (match e with
  | ⟪ K (#_α) (#_β) (#x) (#y) ⟫ => pure x
  | ⟪ S (#_α) (#_β) (#_γ) (#x) (#y) (#z) ⟫ => pure ⟪ (#x) (#z) ((#y) (#z)) ⟫
  | ⟪ M K (T (#α)) (T (#β)) ⟫ => pure ⟪ (#α) → (#β) → (#α) ⟫
  | ⟪ ((#_t_in) → (#t_out)) (#arg) ⟫ => pure t_out
  | ⟪ (#lhs) (#rhs) ⟫ =>
    pure ⟪ (#(eval_unsafe lhs).getD lhs) (#(eval_unsafe rhs).getD rhs) ⟫
  | _ => Option.none).getD e

  if e == e' then
    pure e
  else
    eval_unsafe e'

partial def infer_unsafe : Expr → Except (@TypeError Expr) Expr
  | ⟪ K ⟫ => pure mk_k_type
  | ⟪ S ⟫ => pure mk_s_type
  | ⟪ T ⟫ => pure mk_t_type
  | ⟪ Type ⟫ => pure mk_type_type
  | ⟪ Syntax ⟫ => pure mk_type_syntax
  | ⟪ M K ⟫ => pure mk_m_k_type
  | ⟪ M S ⟫ => pure mk_m_s_type
  | ⟪ -> ⟫ => pure mk_arr_type
  | ⟪ (#f) (#arg) ⟫ => do
    let t_lhs ← infer_unsafe f

    match t_lhs with
    | ⟪ (#t_in) → (#t_out) ⟫ => do
      let t_arg ← infer_unsafe arg

      if t_in == t_arg then
        pure $ (eval_unsafe t_out).getD t_out
      else
        .error (.argument_mismatch t_in t_arg ⟪ (#t_in) → (#t_out) ⟫ arg)
    | _  =>
      let _ ← infer_unsafe ⟪ (#t_lhs) (#arg) ⟫
      pure $ (eval_unsafe ⟪ (#t_lhs) (#arg) ⟫).getD ⟪ (#t_lhs) (#arg) ⟫
  | e => .error (.no_type_not_comb e)

end Expr

#eval toString <$> Expr.infer_unsafe ⟪ (T Type) → (T Type) ⟫

/-
We can interpret K (T Type) (T Type) as a proof or ("constructor") of (T (M K))
We can pattern match on the constructor call to interpret α → β → α.

This isn't congruent with the typing rule, however.
Now we have special cases.

Pattern matching idea.

K α β is a proof of α → β → α

K (M K) _ K y : M K
This is fine.

We don't want to special case M K.
But we want some way to interpret it as α → β → α.

Elaboration within a context?

α → β → α is a constructor for Type.

M K α β = α → β?

It can't be turtles all the way down.
We need to type-check →.
This is just comparing syntax, though.

(t_in → t_out) arg type-checks if type of arg = t_in

M K α β = α → β → α

(t_in → t_out) arg = t_out arg

M K : Type → Syntax

M (M K) : Type → Type → Syntax

app is valid as long as t_left arg type-checks.
It can't be turtles all the way down though.

Type-checking (t_in → t_out) arg requires a special rule.

This is not captured by the type system, because then we would type-check → again.

Recall, T e : Type.

So this doesn't really work.

We need a typing rule for →.
We can't apply something to T whatever.

T is like return.
T and → are our primitives.

→ has special rules.


M K α β = α → β → α

M K α = α → (M (M K)) α
M K α β = α → β → α

K : M K

T should be able to work with anything that produces a Type.
e.g., T Syntax : Type,
but T (M K) : Type → Type → Type

Now for S type.
S is not polymorphic, it's dependent.

M S (α : Type) (β : α → Type) (γ : α → Type) : α → 

S : MS
M S : Type → (T Syntax)

M (M S α) = (α → Type) → (α → Type) → (T Syntax)

M (M S α) α β γ : M (M (M S α)

M S₁ α β γ x = α → β x → γ x
M S₂ α β = α → β x
M S₃ α γ x = α → γ x

M S = (M S₁) → (M S₂) → (M S₃)
S α β γ x y z

x z must be valid, meaning α z must be valid
if α z is valid, then x z is valid.

type of x is such that its type with z applied is valid.

α is a type

generalization of M K.

M K α β is kinda dependent

its type depends on its inputs.

y : α → β x

M Z α γ x = α → γ x

M Y α β x = α → β x

M X α β γ z = α → β x → γ x → M Y 



M X ... x then produces M Y
M y x ... x then produces M z ...

S α β γ : M X α β γ
S α β γ x : (α → β x → γ x)

We need to change the rule for →
such that it produces further outputs,
such that it passes its argument into its output.

assuming (t_in → t_out) arg = t_out arg, which we already have,
S α β γ : (α → β → γ) → (α → β) → (α → γ)

What if we keep → as it is.

We should be able to do S → →

But 

γ : α → T Syntax

M S α β = (α → Type)

M S : Type → T Syntax

S α β γ (x : α → β x → γ x) (y : α → β x) (z : α)

We can't quote to syntax arbitrarily.


M S α β γ x y z = (α → β z → γ z) → (α → β z) → (α → γ z)

We can probably do a fancy typing rule for this.

M K is isomorphic to α → β → α

M K ≅ α → β → α

Two things are isomorphic if for all inputs, they produce the same outputs.

This is like "interpretation"

M S ≅ the actual S type.

≅ is symmetric.

α → β → α ≅ M K

M X is isomorphic to α → β z → γ x at z

This simplifies our typing rule significantly.

We can say a function app is well-typed if its type is isomorphic to t_in -> t_out at z

S : (M X) → (M Y) → (M Z)

iso : ∀ f₁ in, f₁ in = f₂ in

iso x (M X) (whatever)

type of S is an algorithm for how to type-check S

x just needs to be something isomorphic to M X

M X α β γ x = α → (β x) → (γ x)

Two things are obviously isomorphic if they are syntactically equivalent.

M X : α → T Syntax

M X z = α → β x → γ x

M Y z = α → β x

M Z z = α → γ x

S : M X → M Y → M Z

Keep running with the isomorphism idea.

Two things are isomorphic if they are syntactically equivalent.
This is the current level we have.

With our current set up, it is impossible to dependently instantiate K.

This boils down to the same issue as

M K should also be of type T Syntax.

It's just a different "constructor."

M K is a constructor for type.

M K : Type → Type → (T Syntax)

But that would mean:

M K : Type → Type → Type

We could wrap this in T.

But even then,

M K : T (Type → Type → Type)

It's not a Type.

To be consistent,

M K : T (Type → Type → Type)

Introducing new type constructors:

my_type (α : Type) (β : Type) = T (M my_type)

This is a type formation rule.

my_type : α → β → T (M my_type)

But what stops us from saying

my_type₂ : α → β → T (M my_type)?

We should just do

my_type : α → β → T (M my_type)

Or we can do

my_type : α → β → T

so my_type is a constructor for type.

Syntax : T

Type : T

We really don't need Type.

my_type α β : T

There is really no purpose of the Syntax argument.

T has no type.
There should be no circumstance in which it occurs.

K has no effects.

K has the context x can be formed with α

x has the context that it is well-typed at α.

x is "possibly well-typed"

K is definitely well-typed.

if x is definitely well-typed, then K x y is definitely well-typed.

K is definitely well-typed.

K is well-typed at α

α → β is well-typed at Type

T is well-typed if: T → T

args are some circumstance under which it is well-typed.

T : T → T

T x is the assertion x is well-typed.

T x → T x is always true.

T x t is the asesrtion x is well-typed at α. Do we need this?
T x is a proof that x is well-typed.

T x = the type of x.

type : T x

this is the proof that x is well-typed.

K : T x → T y → x

K is always well-typed.

K : T K

t_of_t_axiom : T x → T (T x)

axiom_k₁ : T (T α) → T (K (T α))
axiom_k₂ : T (T α) → T (T β) → T (K (T α) (T β))
axiom_k₃ : T (T α) → T (T β) → T α → T (K (T α) (T β) α)
axiom_k_call : T (T α) → T (T β) → T α → T β → T (K (T α) (T β) α β)

axiom_k is the assertion K is well-typed.

K (T K) (T K) K K

axiom_k is a proof of T K.

axiom_k : T K := Syntax
axiom_s : T S := Syntax

axiom_k_call : T (T α) → T (T β) → T α → T α → T (K (T α) (T β))
-/
