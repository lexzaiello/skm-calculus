import Mathlib.Tactic

/-
# Synthesizing Expressions with Eta-Reduction

In the previous chapter, we saw that we can create an expression representing the nondependent \\(\rightarrow\\) type. However, \\(K\\) and \\(S\\) are dependent. I make use of a translation algorithm to generate point-free expressions involving only \\(S\\), \\(K\\), and \\(M\\) for these expressions.

## Syntax Tree

As outlined prior, our core language consists only of the objects \\(S\\), \\(K\\), \\(M\\), and \\(\text{Type}_{n}\\). I define the syntax-tree in Lean as such:
-/

inductive Expr where
  | s    : Expr
  | k    : Expr
  | m    : Expr
  | ty   : ℕ    → Expr
  | call : Expr → Expr → Expr

/-
For translation purposes, I define an AST for the (optionally) simply-typed \\(\lambda\\)-calculus, extended with our syntax tree. I use de bruijn indices to refer to variables.
-/

inductive LExpr where
  | var   : ℕ     → LExpr
  | call  : LExpr → LExpr → LExpr
  -- Abstraction with binder type
  | lam  : LExpr → LExpr → LExpr
  | m     : LExpr
  | s     : LExpr
  | k     : LExpr
  | ty    : ℕ → LExpr

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

Note that in order to represent explicit typing in (nondependent) \\(\lambda\\)-abstraction types, we require an \\(\Eta\\)-expanded representation of \\(A \rightarrow B\\). I use the same definition I outlined prior:
-/

-- Neither here are point-free
-- This is what we are trying to generate
def mk_arrow_lc (a b : LExpr) : LExpr :=
  (.call (.call (.call .k (.call .m b)) a) b)

def mk_arrow (a b : Expr) : Expr := SKM[(((K (M b)) a) b)]

infix:20 "l~>" => mk_arrow_lc
infix:20 "~>"  => mk_arrow

-- To eliminate λ-abstraction as much as possible
def lift (e : LExpr) : LExpr :=
  match e with
    | (.lam t (.var 0)) =>
      (.call
        (.call
          -- Duplicator S
          (.call (.call (.call .s (t l~> ((t l~> t) l~> t))) (t l~> (t l~> t))) t)
          -- First K, takes (x : t) and (K x)
          (.call (.call .k t) (t l~> t)))
          -- Second K, takes only one (x : t)
          (.call (.call k t) t)
        )
      )
      sorry
    | (.lam t (.call e₁ e₂)) =>
      sorry
    | (.lam t (.var n)) =>
      sorry
    | (.lam t c) =>
      sorry
    | (.call e₁ e₂) =>
      .call (lift e₁) (lift e₂)
    | x => x

