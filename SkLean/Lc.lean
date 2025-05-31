/-
# Typed and Untyped Lambda Calculus

## Untyped Lambda Calculus

### Expressions

The [lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus) is a widely-known model of computation based on variable substitution within anonymous functions.

A lambda expression is defined by the grammar:

$$
e ::= (\lambda x.e)\ |\ e\ e\ |\ x
$$

\\(\lambda x.e\\) represents an anonymous function with body \\(e\\) and a bound variable \\(x\\). \\(e\ e\\) represents function application. \\(x\\) represents a variable.

A variable is said to be "bound" if a corresponding binder in a lambda abstraction is in scope. A variable is said to be free if no such binder exists.

We can encode a lambda expression in Lean like so:
-/

import Mathlib.Tactic

inductive Expr where
  | var : String → Expr
  | app : Expr   → Expr  → Expr
  | abstraction : String → Expr → Expr
deriving Repr

/-
### Evaluation

An expression can be evaluated using the "beta reduction" rule:

$$
((\lambda x.M)\ N) =_{\beta} M[x := N]
$$

This rule denotes that a function application is "beta equivalent" to the body of the function being called, with \\(N\\) substituted in for every instance of \\(x\\) within \\(M\\).

This system of computation is powerful, and known to be turing-complete. However, expressing infinitely reducible expressions is quite easy:

$$
(\lambda x.x\ x)(\lambda x.x\ x)
$$

In Lean, this is not allowed. Let us prove such by defining substitution and evaluation for our AST:
-/

def substitute (for_var : String) (in_expr : Expr) (with_expr : Expr) : Expr :=
  match in_expr with
    | .var v =>
      if v == for_var then
        with_expr
      else
        .var v
    | .app lhs rhs =>
      let lhs' := substitute for_var lhs with_expr
      let rhs' := substitute for_var rhs with_expr

      .app lhs' rhs'
    | .abstraction v body =>
      let body' := (substitute for_var body with_expr)

      .abstraction v body'

#eval substitute "x" (Expr.abstraction "x" (Expr.var "x")) (Expr.var "y")
-- => Expr.abstraction "x" (Expr.var "y")

/-
Our substitution function appears to work as expected.

However, we will run into issues with substitution in functions where variable names collide. [De Bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index) provide a natural solution to this problem.

#### De Bruijn Indices

De Bruijn indices prevent variables from being shadowed by referring to bound varaibles by their position relative to the binder. For example, the identity function:

$$
(\lambda 1) e =_{\beta} e
$$

We can revise our Lean definition to utilize De Bruijn indices like such:
-/

inductive Expr' where
  | var : ℕ     → Expr'
  | app : Expr' → Expr' → Expr'
  | abstraction : Expr' → Expr'
deriving Repr

/-
We will also have to update substitute to reflect this change.

A simple algorithm for variable substitution in De Bruijn-indexed expressions simply increments a "depth" counter until it reaches a variable with \\(n = \text{depth}\\), then replaces the value.
However, free variables need to be accounted for.
In the case of the expression being substituted in, for every deeper level in the tree which it is inserted in, its free variables msut be incremented by 1.
-/

-- Shifts free variable de bruijn indices by the specified amount
-- each layer deeper, the shift becomes larger
def with_indices_plus (in_expr : Expr') (shift_by : ℕ) : Expr' :=
  match in_expr with
    | .abstraction body =>
      .abstraction (with_indices_plus body shift_by.succ)
    | .var n =>
      if n > shift_by then
        .var (n + shift_by)
      else
        .var n
    | .app lhs rhs =>
      .app (with_indices_plus lhs shift_by) (with_indices_plus rhs shift_by)

def substitute' (in_expr : Expr') (n : ℕ) (with_expr : Expr') : Expr' :=
  match in_expr with
    | .abstraction body =>
      .abstraction (substitute' body n.succ with_expr)
    | .var n' => if n == n' then with_indices_plus with_expr n else .var n'
    | x => x

/-
#### `partial` Evaluation with Unfounded Recursion

We may now attempt to write an evaluation function. Evaluation should continually perform substitution until no function applications remain at the outermost layer of the expression.
-/

partial def eval (e : Expr') : Expr' :=
  match e with
    | .app (.abstraction body) rhs =>
      eval (substitute' body 0 rhs)
    | .app lhs rhs =>
      eval (.app (eval lhs) rhs)
    | x => x

/-
Unfortunately, this will not compile without the keyword "partial" in Lean, as it could potentially run forever (i.e., uses unfounded recursion). As a result, proving properties about this function is impossible in Lean, as it cannot reason about the function in a manner consistent with its type system.

## Simply-Typed Lambda Calculus

The simply-typed lambda calculus prevents infinitely reducing expressions from being expressed by assigning types to expressions:

$$
\tau ::= \tau \rightarrow \tau\ |\ T
$$

where \\(T\\) is the type of a constant value (a "base type"), and \\(\alpha \rightarrow \beta\\) is the type of a function with a bound variable of type \\(\alpha\\) and a body of type \\(\beta\\). We can then type the bound variable of a lambda abstraction like so:

$$
(\lambda x : \text{Nat}.x + 1)
$$

We can then encode typed lambda expressions in Lean like so:
-/

inductive Base where
  | int : Base
  | nat : Base
deriving DecidableEq, BEq, Repr

inductive Ty where
  | base  : base → Ty
  | arrow : Ty   → Ty → Ty
deriving DecidableEq, BEq, Repr

open Base
open Ty

/-
For example, the type of the function \\((\lambda x : \text{Nat}.x + 1)\\) would be `Nat → Nat`, or:
-/

#check arrow (base nat) (base nat)

/-
In order to prevent ill-formed expressions from being inputted, we can define typing judgement rules that verify the correctness of a typing.

We will follow these judgement rules:
- If a variable is bound by an abstraction with a binder of type \\(\alpha\\), then the variable is of type \\(\alpha\\).
- If a constant \\(c\\) is of type \\(T\\), it is of type \\(T\\).
- If a lambda abstraction's binder is of type \\(t\\) and its body of type \\(t'\\), it is of type \\(t \rightarrow t'\\).
- In an application \\(e_{1}\ e_{2}\\), the left hand side expression must be of a type of the form \\(\alpha \rightarrow \beta\\). The application argument \\(e_{2}\\) must have type \\(\alpha\\). The entire expression is of type \\(\beta\\).

We will also define a mapping from constant values to types:
-/

inductive Cnst where
  | num : ℕ → Cnst
  | int : ℤ → Cnst
deriving DecidableEq, BEq, Repr

def type_of_cnst : Cnst → Base
  | .num _ => .nat
  | .int _ => .int

/-
We will extend `Expr` to include our constant values and binder (\\(x : \alpha\\)) typings.
-/

inductive Expr'' where
  | cnst : Cnst      → Expr''
  | var : ℕ          → Expr''
  | app : Expr''     → Expr'' → Expr''
  | abstraction : ty → Expr''  → Expr''
deriving BEq, Repr, DecidableEq

/-
In order to represent the types of variables, we will maintain a stack of types of the nearest abstraction binders (e.g., \\(\lambda x : \alpha.x\\)). We can determine the type of a variable by looking up its type in this "context."
-/

-- Indexed relative to de bruijn index of variable being type-checked
abbrev Ctx := List Ty

def type_of (ctx : Ctx) : Expr'' → Option Ty
  | .cnst c => some (.base (type_of_cnst c))
  -- Expression variables are 1-indxed, list is zero-indxed
  | .var (n + 1) => ctx[n]?
  | .var _ => none
  -- Lhs must eventually evaluate to an abstraction
  -- and rhs must eventually evaluate to the type of the bound variable in lhs
  | .app lhs rhs => do
    let t_lhs ← type_of ctx lhs
    let t_rhs ← type_of ctx rhs

    match t_lhs with
      | arrow in_t out_t =>
        if in_t != t_rhs then
          none
        else
          pure (out_t)
      | _ => none
  | .abstraction bind_ty body => do
    let ctx' := bind_ty :: ctx

    some (.arrow bind_ty (← type_of ctx' body))

/-
Let's try out or type inference function for a few functions:

1. Identity function for nats: \\(\lambda x : \mathbb{N}.x\\)
-/

#eval type_of [] (.abstraction (.base .nat) (.var 1))
-- => some (Ty.arrow (Ty.base (Base.nat)) (Ty.base (Base.nat)))

/-
2. Application of identity function with a nat: \\((\lambda x : \mathbb{N}.x) 1\\) => 1
-/

#eval type_of [] (.app (.abstraction (.base .nat) (.var 1)) (.cnst (.num 1)))
-- => some (Ty.base (Base.nat))

/-
Nice.

Now that our expressions are typed, we may be able to rewrite our `eval` function in a verifiably terminating way that Lean likes. In doing so, we must prove **strong normalization** of our simply-typed lambda calculus.

In the [next chapter](./SnLc.lean.md), I elaborate more on strong normalization.

-/
