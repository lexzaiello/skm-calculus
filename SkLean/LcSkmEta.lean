/-
# Synthesizing Expressions with \\(\eta\\)-Reduction

In the previous chapter, we saw that we can create an expression representing the nondependent \\(\rightarrow\\) type. However, \\(K\\) and \\(S\\) are dependent. I make use of a translation algorithm to generate point-free expressions involving only \\(S\\), \\(K\\), and \\(M\\) for these expressions.

## Syntax Tree

As outlined prior, our core language consists only of the objects \\(S\\), \\(K\\), \\(M\\), and \\(\text{Type}_{n}\\). I define the syntax-tree in Lean as such:
-/

import Mathlib.Tactic


inductive Expr where
  | s    : Expr
  | k    : Expr
  | m    : Expr
  | ty   : ℕ    → Expr
  | call : Expr → Expr → Expr
deriving Repr

namespace Expr

def toStringImpl (e : Expr) : String :=
  match e with
    | .k          => "K"
    | .s          => "S"
    | .m          => "M"
    | .ty n       => s!"Type {n}"
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
  -- Abstraction with binder type
  | lam  : LExpr → LExpr → LExpr
  | m     : LExpr
  | s     : LExpr
  | k     : LExpr
  | ty    : ℕ → LExpr
  | arrow : LExpr → LExpr → LExpr
deriving Repr

namespace LExpr

def toStringImpl (e : LExpr) : String :=
  match e with
    | .var n            => s!"var {n}"
    | .raw e            => s!"{e}"
    | .call e₁ e₂       => s!"({e₁.toStringImpl} {e₂.toStringImpl})"
    | .lam t body       => s!"λ :{t.toStringImpl}.{body.toStringImpl}"
    | .m                => "M"
    | .k                => "K"
    | .s                => "S"
    | .ty n             => s!"Type {n}"
    | .arrow t_in t_out => s!"{t_in.toStringImpl} → {t_out.toStringImpl}"

end LExpr

instance : ToString LExpr where
  toString := fun e => e.toStringImpl

/-
## DSL

I make use of a small DSL for readability purposes for both my \\(\lambda\\) and \\(SK(M)\) syntax trees:
-/

declare_syntax_cat skmexpr
syntax "K"                                                             : skmexpr
syntax "S"                                                             : skmexpr
syntax "M"                                                             : skmexpr
syntax "Ty" term                                                       : skmexpr
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
  | `(⟪ Ty $e:term ⟫)                  => `(Expr.ty $e)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)   => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

/-
## Translation

Translation of all terms except \\(\lambda\\)-abstraction is obvious. For \\(\lambda\\)-abstraction, we utilize the 3 rules:

### \\(I\\)-transformation

$$
\lambda : t.0 \mapsto (SKK : t \rightarrow t)
$$

### \\(S\\)-transformation

$$
\lambda : t.e_{1}\ e_{2} \mapsto S\ (\lambda : t.e_{1}) (\lambda : t.e_{2})
$$

### \\(K\\)-transformation

$$
\frac{\Gamma \vdash c : t_{1}}{(\lambda : t.c \mapsto K\ t_{1}\ t\ c)}
$$

For brevity, I have omitted explicit typing calls to the combinators in some places, though we will see how this is derived soon.

### Lean Implementation

Note that in order to represent explicit typing in (nondependent) \\(\lambda\\)-abstraction types, we require an \\(\eta\\)-expanded representation of \\(A \rightarrow B\\). I use the same definition I outlined prior:
-/

-- Neither here are point-free
-- This is what we are trying to generate
def mk_arrow (a b : Expr) : Expr := SKM[(((K (M b)) a) b)]

infix:20 "~>"  => mk_arrow

/-
I make use of a simple, partial `type_of` function which is required to derive the "in-between" and output type in the \\(S\\) transformation, since only the input type is known.
-/

namespace Expr

def type_of_unsafe (e : Expr) : Option Expr :=
  match e with
    | .ty n => pure $ .ty n.succ
    | SKM[M] => pure SKM[(M M)]
    | SKM[K] => pure SKM[(M K)]
    | SKM[S] => pure SKM[(M S)]
    | SKM[((K α) β)] => pure $ α ~> (β ~> α)
    | SKM[(((S α) β) γ)] => pure $ (α ~> (β ~> γ)) ~> ((α ~> β) ~> α)
    | SKM[(lhs _rhs)] =>
      match type_of_unsafe lhs with
        | .some SKM[(((K _β) α) β)] =>
          β
        | _ => none

end Expr

def type_of (ctx : List LExpr) (e : LExpr) : Option LExpr :=
  match e with
    | .raw e => (.raw .) <$> e.type_of_unsafe
    | (.lam t (.var 0)) =>
      some $ LExpr.arrow t t
    | (.lam t (.var n)) => do
      pure $ (.arrow t (← ctx[n.pred]?))
    | (.lam t body) => do
      some (.arrow t $ (← type_of (t :: ctx) body))
    | .ty n => some $ .ty n.succ
    | a@(.arrow _ _) => some $ .call .m a
    | (.call (.call .k α) β) =>
      pure (.arrow α (.arrow β α))
    | (.call (.call (.call .s α) β) γ) =>
      pure ((.arrow (.arrow α (.arrow β γ)) (.arrow (.arrow α β) α)))
    | (.call .m e) =>
      type_of ctx e
    | .k => pure $ .call .m .k
    | .s => pure $ .call .m .s
    | .m => pure $ .call .m .m
    | .call lhs _ => do
      match ← type_of ctx lhs with
        | (.arrow _ out_t) => pure out_t
        | .raw SKM[(((K (M _β)) α) β)] => pure $ .raw β
        | _ => none
    | .var n => ctx[n]?

def dec_vars (depth : ℕ) (e : LExpr) : LExpr :=
  match e with
    | .var n =>
      if n > depth then
        .var n.pred
      else
        .var n
    | .call lhs rhs => .call (dec_vars depth lhs) (dec_vars depth rhs)
    | .arrow t_in t_out => .arrow (dec_vars depth t_in) (dec_vars depth t_out)
    | .lam t body => .lam (dec_vars depth.succ t) (dec_vars depth.succ body)
    | x => x

-- To eliminate λ-abstraction as much as possible
-- This function abstracts variable 0 from a lambda-free body.
partial def lift (ctx : List LExpr) (e : LExpr) : LExpr :=
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
      (.call (lift ctx lhs) (lift ctx rhs))
    | .lam t_in (.call lhs rhs) =>
      let lhs' := lift (t_in :: ctx) lhs |> fun body => .lam t_in body
      let rhs' := lift (t_in :: ctx) rhs |> fun body => .lam t_in body

      let t_lhs := (type_of ctx lhs').getD (.call .m lhs')
      let t_rhs := (type_of ctx rhs').getD (.call .m rhs')

      lift ctx (.call (.call (.call (.call (.call .s t_lhs) t_rhs) t_in) lhs') rhs')
    | .arrow t_in t_out =>
      let t_in'  := lift ctx t_in
      let t_out' := lift ctx t_out

      .arrow t_in' t_out'
    | .lam t (.var 0) =>
      let t' := lift ctx t

      (.call (.call (.call (.call
          (.call .s ((.arrow t' (.arrow (.arrow t' t') t'))))
            (.arrow t' (.arrow t' t'))) t')
            (.call (.call .k t') (.arrow t' t')))
              (.call (.call .k t') t'))
    | .lam t_in₀ (.lam t_in₁ x') =>
      let t_in₀' := lift ctx t_in₀

      let body' := lift (t_in₀' :: ctx) (.lam t_in₁ x')

      lift ctx (.lam t_in₀' body')
    | .lam t_in x =>
      let t_in' := lift ctx t_in
      let x' := lift ctx x |> dec_vars 0
      let t_x' := (type_of (t_in' :: ctx) x').getD (.call .m x')

      lift ctx (.call (.call (.call .k t_x') t_in') x')
    | e => e

    e'

def to_sk (e : LExpr) : Option Expr :=
  match e with
    | .ty n  => SKM[Ty n]
    | .call lhs rhs => do
      SKM[(#(← to_sk lhs) #(← to_sk rhs))]
    | .k => SKM[K]
    | .s => SKM[S]
    | .m => SKM[M]
    | .arrow t_in t_out => do
      let t_in'  ← to_sk t_in
      let t_out' ← to_sk t_out

      t_in' ~> t_out'
    | .raw e => e
    | _ => SKM[Ty 0]

def to_sk_unsafe (e : LExpr) : Expr :=
  match e with
    | .ty n  => SKM[Ty n]
    | .call lhs rhs =>
      SKM[(#(to_sk_unsafe lhs) #(to_sk_unsafe rhs))]
    | .k => SKM[K]
    | .s => SKM[S]
    | .m => SKM[M]
    | .arrow t_in t_out =>
      let t_in' := to_sk_unsafe t_in
      let t_out' := to_sk_unsafe t_out

      t_in' ~> t_out'
    | .raw e => e
    | _ => SKM[Ty 0]

/-
We can now define the \\(\rightarrow\\) expression using our \\(\lambda\\)-calculus AST and translate to \\(SK(M)\\) using our `lift` and `to_sk` functions. Note that since universes are stratified, \\(\rightarrow\\) is polymorphic at the meta level to universe levels. In practice, the compiler generates an \\(\rightarrow\\) expression for all universes used in the program. Furthermore, universes above \\(1\\) are rarely used.
-/

def arrow_lc (u v : ℕ) : LExpr := (.lam (.ty u) (.lam (.ty v) (.call (.call (.call .k (.call .m (.var 0))) (.var 1)) (.var 0))))

/-
For testing purposes, we will write `partial` evaluation and typing functions:
-/

def eval_n (n : ℕ) (e : Expr) : Expr :=
  if n = 0 then
    e
 else
   let e' := match e with
     | SKM[((((K _α) _β) x) _y)] => x
     | SKM[((((((S _α) _β) _γ) x) y) z)] => SKM[((x z) (y z))]
     | SKM[(lhs rhs)] =>
       SKM[((#(eval_n n.pred lhs)) #(eval_n n.pred.pred rhs))]
     | x => x

   eval_n n.pred.pred.pred e'

#eval (.call (.call (.lam (.ty 0) (.lam (.ty 0) (.var 0))) (.ty 2)) (.ty 3))
  |> lift []
  |> to_sk_unsafe
  |> eval_n 15

def arrow (u v : ℕ) : Expr := arrow_lc u v
  |> lift []
  |> to_sk_unsafe
  |> eval_n 30

#eval arrow 0 0

def parse_arrow (e : Expr) : String :=
  match e with
    | SKM[(((K (M _b)) a) b)] =>
      let a' := (parse_arrow a)
      let b' := (parse_arrow b)

      s!"({a'} -> {b'})"
    | _ => s!"{e}"

#eval (.call (.call (.lam (.ty 1) (.lam (.ty 1) (.var 0))) (.ty 1)) (.ty 0)) |> (lift [] . >>= to_sk >>= fun e => pure $ eval_n 10 e)

/-
As a test, let's see if we can construct an arrow from \\(\text{Type} \rightarrow \text{Type}\\). Note that these examples are not intended to typecheck, merely to demonstrate that the translation is coherent.

Here is \\(\text{Type} \rightarrow \text{Type}\\):
-/

#eval (parse_arrow ∘ eval_n 25) SKM[(((#(arrow 0 1)) (Ty 0)) (Ty 1))]

/-
This evaluates to \\(\text{Type} \rightarrow \text{Type}\\). Furthermore, it behaves similarly to \\(\forall\\), in that "substitution" (application) produces the output type:
-/

#eval eval_n 10 SKM[((((#(arrow 0 0)) (Ty 0)) (Ty 0)) S)]

/-
This evaluates to `Type 0`.

In the next chapter, we will see how we can explicitly type \\(K\\) using this \\(\rightarrow\\) expression derived from our combinators.

I persist the definition of \\(\rightarrow\\) to a file in this repository.

-/

#eval (Expr.type_of_unsafe SKM[((((K (Ty 1)) (Ty 3)) (Ty 0)))]).map parse_arrow
#eval ((Expr.type_of_unsafe) $ arrow 0 0).map parse_arrow
