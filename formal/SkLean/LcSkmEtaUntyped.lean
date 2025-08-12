/-
# Synthesizing Expressions with \\(\eta\\)-Reduction

In the previous chapter, we saw that we can create an expression representing the nondependent \\(\rightarrow\\) type. However, \\(K\\) and \\(S\\) are dependent. I make use of a translation algorithm to generate point-free expressions involving only \\(S\\), \\(K\\), and \\(M\\) for these expressions.

## Syntax Tree

As outlined prior, our core language consists only of the objects \\(S\\), \\(K\\), \\(M\\), and \\(\text{Type}_{n}\\). I define the syntax-tree in Lean as such:
-/

import Mathlib.Tactic
import SkLean.Ast3

namespace Expr

def toStringImpl (e : Expr) : String :=
  match e with
    | .k          => "K"
    | .s          => "S"
    | .m          => "M"
    | .m₀         => "M₀"
    | .s₀         => "S₀"
    | .k₀         => "K₀"
    | .prp        => "Prop"
    | .call e₁ e₂ => s!"({toStringImpl e₁} {toStringImpl e₂})"

end Expr

instance : ToString Expr where
  toString := fun e => e.toStringImpl

  /-
For translation purposes, I define an AST for the (optionally) simply-typed \\(\lambda\\)-calculus, extended with our syntax tree. I use de bruijn indices to refer to variables.
-/

inductive LExpr where
  | var   : ℕ     → LExpr
  | call  : LExpr → LExpr → LExpr
  | raw   : Expr  → LExpr
  | lam   : LExpr → LExpr
  | m     : LExpr
  | s     : LExpr
  | k     : LExpr
deriving Repr

namespace LExpr

def toStringImpl (e : LExpr) : String :=
  match e with
    | .var n            => s!"var {n}"
    | .raw e            => s!"{e}"
    | .call e₁ e₂       => s!"({e₁.toStringImpl} {e₂.toStringImpl})"
    | .lam body       => s!"λ {body.toStringImpl}"
    | .m                => "M"
    | .k                => "K"
    | .s                => "S"

end LExpr

instance : ToString LExpr where
  toString := fun e => e.toStringImpl

namespace Expr

def dec_vars (depth : ℕ) (e : LExpr) : LExpr :=
  match e with
    | .var n =>
      if n > depth then
        .var n.pred
      else
        .var n
    | .call lhs rhs => .call (dec_vars depth lhs) (dec_vars depth rhs)
    | .lam body => .lam (dec_vars depth.succ body)
    | x => x

-- To eliminate λ-abstraction as much as possible
-- This function abstracts variable 0 from a lambda-free body.
partial def lift (e : LExpr) : LExpr :=
  -- We shouldn't really do anything unless
  -- the expression is a lambda abstraction
  -- In the case of e₁ e₂ application,
  -- we must lift both e₁ and e₂ first,
  -- then apply the S-transformation
  -- In the case of lambda abstraction with (.var 0)
  -- as the body, apply the I-transformation
  -- In the case of lambda abstraction with
  -- any other variable which is not free
  -- we decrement the index, since
  -- one abstraction has been removed
  let e' := match e with
    | .call lhs rhs =>
      (.call (lift lhs) (lift rhs))
    | .lam (.call lhs rhs) =>
      let lhs' := lift lhs |> LExpr.lam
      let rhs' := lift rhs |> LExpr.lam

      lift (.call (.call .s lhs') rhs')
    | .lam (.var 0) =>
      (.call (.call .s .k) .k)
    | .lam (.lam x') =>
      let body' := lift (.lam x')

      lift (.lam body')
    | .lam x =>
      let x' := lift x |> dec_vars 0

      lift (.call .k x')
    | e => e

    e'

def to_sk (e : LExpr) : Option Expr :=
  match e with
    | .call lhs rhs => do
      SKM[(#(← to_sk lhs) #(← to_sk rhs))]
    | .k => SKM[K]
    | .s => SKM[S]
    | .m => SKM[M]
    | .raw e => e
    | _ => none

def to_sk_unsafe (e : LExpr) : Expr :=
  match e with
    | .call lhs rhs =>
      SKM[(#(to_sk_unsafe lhs) #(to_sk_unsafe rhs))]
    | .k => SKM[K]
    | .s => SKM[S]
    | .m => SKM[M]
    | .raw e => e
    | _ => SKM[K]

/-
We can now define the \\(\rightarrow\\) expression using our \\(\lambda\\)-calculus AST and translate to \\(SK(M)\\) using our `lift` and `to_sk` functions. Note that since universes are stratified, \\(\rightarrow\\) is polymorphic at the meta level to universe levels. In practice, the compiler generates an \\(\rightarrow\\) expression for all universes used in the program. Furthermore, universes above \\(1\\) are rarely used.
-/

def arrow_lc : LExpr := (.lam (.lam (.call (.call (.call .k (.call .m (.var 0))) (.var 1)) (.var 0))))

/-
For testing purposes, we will write `partial` evaluation and typing functions:
-/

-- Type of K : λ α.→ (M α) (λ β.(→ (M β)) (M α))
def Flse := (LExpr.raw (.call .s (.call (.call .s .k) .k)))
def Tre  := (LExpr.raw .k)

def And := (LExpr.lam (.lam (.call (.call (.var 1) (.var 0)) (.var 1))))

-- Type of K : ∀ t x y h, (M h (M x t)) ∧ h t False
def t_k := (.lam (.lam (.lam (.lam (.call (.call And (.call (.call (.raw .m) (.var 0)) (.var 3))) (.call (.call (.var 0) (.var 3)) Flse))))))
  |> lift
  |> to_sk_unsafe

-- Type of S : ∀ t x y z (h : M ((x z) (y z)) t), h t False
def t_s := (.lam (.lam (.lam (.lam (.lam (.call (.call (.var 0) (.var 4)) Flse))))))
  |> lift
  |> to_sk_unsafe

-- Type of M : ∀ e, ((M e) (M e))
def t_m := (LExpr.call (.call (.raw .s) (.raw .m)) (.raw .m))

#eval t_k |> ToString.toString
#eval t_s
#eval t_m

def eval_n (n : ℕ) (e : Expr) : Expr :=
  if n = 0 then
    e
 else
   let e' := match e with
     | SKM[((K x) _y)] => x
     | SKM[(((S x) y) z)] =>
       let x' := eval_n n.pred x
       let y' := eval_n n.pred.pred y
       let z' := eval_n n.pred.pred z
       SKM[((x' z') (y' z'))]
     | SKM[(M (lhs rhs))] =>
       let lhs' := eval_n n.pred lhs
       let rhs' := eval_n n.pred rhs
       SKM[(t_out ((M lhs') rhs'))]
     | SKM[(M K)] => t_k
     | SKM[(M S)] => t_s
     | SKM[(M M)] => t_m
     | SKM[(lhs rhs)] =>
       SKM[((#(eval_n n.pred lhs)) #(eval_n n.pred.pred rhs))]
     | x => x

   if e' == e then
     e
   else
     eval_n n.pred.pred.pred e'

partial def eval_unsafe (e : Expr) : Expr :=
  let e' := match e with
     | SKM[((K x) _y)] => x
     | SKM[(((S x) y) z)] =>
       let x' := eval_unsafe x
       let y' := eval_unsafe y
       let z' := eval_unsafe z

       SKM[((x' z') (y' z'))]
     | SKM[(M (lhs rhs))] =>
       let lhs' := eval_unsafe lhs
       let rhs' := eval_unsafe rhs

       SKM[(t_out ((M lhs') rhs'))]
     | SKM[(M K)] => t_k
     | SKM[(M S)] => t_s
     | SKM[(M M)] => t_m
     | SKM[(lhs rhs)] =>
       SKM[((#(eval_unsafe lhs)) #(eval_unsafe rhs))]
     | x => x

   if e' == e then
     e
   else
     eval_unsafe e'

#eval s!"{t_k}"
#eval s!"{t_s}"
#eval s!"{t_m}"

#eval eval_n 40 SKM[((t_k K) S)] == t_k
-- => true
#eval eval_n 50 SKM[(M (((S K) K) K))] == t_k
-- => true

-- Church numeral example

def mk_church (n : ℕ) : LExpr :=
  let rec mk_church_body (n : ℕ) : LExpr :=
    if n = 0 then
      (.var 0)
    else
      (.call (.var 1) (mk_church_body n.pred))

  (.lam (.lam $ mk_church_body n))

def n_0 := mk_church 0
  |> lift
  |> to_sk_unsafe

def n_1 :=  mk_church 1
  |> lift
  |> to_sk_unsafe

def succ := (.lam (.lam (.lam (.call (.var 1) (.call (.call (.var 2) (.var 2)) (.var 0))))))
  |> lift
  |> to_sk_unsafe

