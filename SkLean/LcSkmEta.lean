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
    | .var n            => s!"{n}"
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

Note that in order to represent explicit typing in (nondependent) \\(\lambda\\)-abstraction types, we require an \\(\Eta\\)-expanded representation of \\(A \rightarrow B\\). I use the same definition I outlined prior:
-/

-- Neither here are point-free
-- This is what we are trying to generate
def mk_arrow (a b : Expr) : Expr := SKM[(((K (M b)) a) b)]

infix:20 "~>"  => mk_arrow

/-
I make use of a simple, partial `type_of` function which is required to derive the "in-between" and output type in the \\(S\\) transformation, since only the input type is known.
-/

def type_of (ctx : List LExpr) (e : LExpr) : Option LExpr :=
  match e with
    | (.lam t (.var 0)) =>
      some $ .arrow t t
    | (.lam t (.var n)) => do
      pure $ (.arrow t (← ctx[n]?))
    | (.lam t body) => do
      some (.arrow t $ (← type_of (t :: ctx) body))
    | .ty n => some $ .ty n.succ
    | .arrow _ _ => some $ .ty 0
    | (.call (.call .k α) β) =>
      pure (.arrow α (.arrow β α))
    | (.call (.call (.call .s α) β) γ) =>
      pure ((.arrow (.arrow α (.arrow β γ)) (.arrow (.arrow α β) α)))
    | (.call .m e) =>
      type_of ctx e
    | .k => pure $ .call .m .k
    | .s => pure $ .call .m .s
    | .m => pure $ .call .m .m
    | .call lhs _ =>
      match type_of ctx lhs with
        | .some (.arrow _ out_t) =>
          some out_t
        | _ => none
    | .var n =>
      ctx[n]?

-- So that when we remove a λ abstraction, vars are bound correctly
def dec_vars (e : LExpr) : LExpr :=
  match e with
    | (.var $ n + 1) => .var n
    | .lam t body =>
      .lam t $ dec_vars body
    | .call lhs rhs =>
      .call (dec_vars lhs) (dec_vars rhs)
    | .arrow t_in t_out =>
      .arrow (dec_vars t_in) (dec_vars t_out)
    | x => x

-- To eliminate λ-abstraction as much as possible
partial def lift (ctx : List LExpr) (e : LExpr) : Option LExpr :=
  match e with
    | (.lam t (.var 0)) =>
      pure (.call
        (.call
          -- Duplicator S
          (.call (.call (.call .s (.arrow t (.arrow (.arrow t t) t))) (.arrow t (.arrow t t))) t)
          -- First K, takes (x : t) and (K x)
          (.call (.call .k t) (.arrow t t)))
          -- Second K, takes only one (x : t)
        (.call (.call .k t) t))
    | (.lam t (.call e₁ e₂)) => do
      let lam_e₁' ← lift ctx (.lam t e₁)
      let lam_e₂' ← lift ctx (.lam t e₂)

      let t_e₁' ← type_of ctx lam_e₁'
      let t_e₂' ← type_of ctx lam_e₂'

      pure (LExpr.call
        -- S duplicator: e₁ takes in duplicated arg, retains its type
        -- same with e₂
        -- we combine them
        (.call (.call (.call (.call .s t_e₁') t_e₂') t)
        lam_e₁')
        lam_e₂')
    | (.lam t c) => do
      let c' := dec_vars $ (← lift (t :: ctx) c)
      let t_c ← type_of (t :: ctx) c'
      pure (.call (.call (.call .k t_c) t) c')
    | (.call e₁ e₂) => do
      pure (.call (← lift ctx e₁) (← lift ctx e₂))
    | x => x

def to_sk (e : LExpr) : Option Expr :=
  match e with
    | .ty n  => pure SKM[Ty n]
    | .call lhs rhs => do
      pure SKM[(#(← to_sk lhs) #(← to_sk rhs))]
    | .k => pure SKM[K]
    | .s => pure SKM[S]
    | .m => pure SKM[M]
    | .arrow t_in t_out => do
      let t_in' ← to_sk t_in
      let t_out' ← to_sk t_out

      pure $ t_in' ~> t_out'
    | _ => none

/-
We can now define the \\(\rightarrow\\) expression using our \\(\lambda\\)-calculus AST and translate to \\(SK(M)\\) using our `lift` and `to_sk` functions. Note that since universes are stratified, \\(->\\) is polymorphic at the meta level to universe levels. In practice, the compiler generates an \\(->\\) expression for all universes used in the program. Furthermore, universes above \\(1\\) are rarely used.
-/

def arrow_lc (u : ℕ) : LExpr := (.lam (.ty u) (.lam (.ty u) (.call (.call (.call .k (.call .m (.var 0))) (.var 1)) (.var 0))))

def arrow (u : ℕ) := arrow_lc u |> (lift [] .)

#eval arrow 0
