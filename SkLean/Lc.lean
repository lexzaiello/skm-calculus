/-

# Typed and Untyped Lambda Calculus

## Untyped Lambda Calculus

The [lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus) is a widely-known model of computation based on variable substitution within anonymous functions.

A lambda expression is defined by the grammar:

$$
e ::= (\lambda x.e)\ |\ e\ e\ |\ x
$$

\\(\lambda x.e\\) represents an anonymous function with body \\(e\\) and a bound variable \\(x\\). \\(e\ e\\) represents function application. \\(x\\) represents a variable.

A variable is said to be "bound" if a corresponding binder in a lambda abstraction is in scope. A variable is said to be free if no such binder exists.

We can encode a lambda expression in Lean like so:
-/

import Mathlib.Data.Nat.Notation

inductive Expr where
  | var : String → Expr
  | app : Expr   → Expr  → Expr
  | abstraction : String → Expr → Expr
deriving Repr

/-
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
We will also have to update substitute to reflect this change. A simple algorithm for variable substitution in De Bruijn-indexed expressions simply increments a "depth" counter until it reaches a variable with \\(n = \text{depth}\\), then replaces the value. However, free variables need to be accounted for. In the case of the expression being substituted in, for every deeper level in the tree which it is inserted in, its free variables msut be incremented by 1. The inverse is true of free variables in the expression being substituted into.
-/

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
We may now attempt to write an evaluation function. Evaluation should continaully perform substitution until no function applications remain at the outermost layer of the expression. This will not compile without the keyword "partial" in Lean, as it could potentially run forever (i.e., uses unfounded recursion).
-/

partial def eval (e : Expr') : Expr' :=
  match e with
    | .app (.abstraction body) rhs =>
      eval (substitute' body 0 rhs)
    | .app lhs rhs =>
      eval (.app (eval lhs) rhs)
    | x => x

/-
## Simply-Typed Lambda Calculus and Strong Normalization

The simply-typed lambda calculus prevents infinitely reducing expressions from being expressed by assigning types to lamabda abstractions:

$$
\tau ::= \tau \rightarrow \tau\ |\ T
$$

where \\(T\\) is the type of a constant value (a "base type"), and \\(\alpha \rightarrow \beta\\) is the type of a function with a bound variable of type \\(\alpha\\) and a body of type \\(\beta\\). We can then type the bound variable of a lambda abstraction like so:

$$
(\lambda x : Nat.x + 1)
$$

We can naively encode a lambda expression and our types in Lean like so:
-/

inductive Base where
  | nat : Base

inductive Ty where
  | base : Base → Ty
  | arrow : Ty  → Ty → Ty

open Base
open Ty

/-
For example, the type of the function (λx : Nat.x + 1) would be Nat → Nat, or:
-/

#check arrow (base nat) (base nat)

