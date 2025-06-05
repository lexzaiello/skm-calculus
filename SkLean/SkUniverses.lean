/-
# SK Universes

_Note: this section is completely unfinished._

So far, we have seen that \\(K : \alpha \rightarrow \beta \rightarrow \alpha\\). The key insight is that the type of \\(K\\) looks suspiciously similar to the \\(K\\) combinator. We can imagine a system of hierarchied universes of \\(K\\) combinators, where some base \\(K\\) is polymorphic, as in our current calculus.

$$
K_{0} : \forall \alpha, \beta, x : \alpha, y : \beta, \alpha
K_{n + 1} : K_{n} x y = x
$$

Here is an example in Lean:
-/

def K₀ (α : Type) (β : Type) : α → β → α :=
  fun x y => x

/-
We immediately run into issues with this typing. It's not clear how the typing `K₁ : K₀` is useful. How are `α` and `β` substituted?
-/

def K₁ : K₀ := sorry
-- Error: Type expected, got...

/-
Another key observation: the act of dependently typing an expression requires substitution. Aha! The `S` combinator.
`S` duplicataes its argument `z` into `x` and `y` and feeds the result into `x z`. We can imagine a scenario where `x z` creates an expression, `y z` creates a type, and `x z (y z)` creates a dependently-typed function. Ideally, this would behave as such:

```
K₀ : ∀ α β (x : α) (y : β), α
K₁ α β = (something : K₀ α β)
K₁ α   = S₀ K₀ _ α = K₀ α (_ α)
_ α β = α → β → a
_ = K₀?
_ =

K_type : α = ∀ α β (x : α) (y : β), α
K_term α β : ∀ (x : α) (y : β), α x y = α

K₁ : K₀
K₁ α : K₀ α
K₁ α β : K₀ α β → (K₁ α β : α)
```

Interesting symmetry between `K_type` and `K_term`. Working backwards,

```
α : Type m
β : Type n
K₁ α β : K₀ α β  = K₀ α β
```

Contradiction? How can `K₀ α β` be of type `K₀ α β`?

What about:

```
K₁ α β : Kt₀ α β = K₀ α β
```

where `Kt₀ α β = α → β → α`. How is Kt₀ defined?

```
Kt₀ α β = ∀ x : α, y : β, α
Kt₀ : ∀ (α : Type m) (β : Type n), Type m = Kt₁
```

Interesting...

```
Kt_{n, m} : Type (m + 1) = ∀ (x : Type m) (y : Type n), x
Kt_{0, 0} : Type 1 = ∀ (x : Type 0) (y : Type 0), Type 0
```

This judgement intuitively holds (a la Calculus of Constructions)

```
K_t = ∀ (x : ?1) (y : ?2), x
K_t : ?1
K_thing = ∀ α : Type, β : Type, K_t
K_thing[α := ℕ, β := ℝ] → K_thing = ∀ (x : α) (y : β), x
K_thing : (x : α)
```

We can say that `K_t` is only well-typed under a context Γ where `x : something ∧ y : something₂`.

However, to define the `K` combinator, we need some way to instantiate `(.var 3) and (.var 3₁)` at the expression level.

```
((K α β) : K₀[?1 := α, ?2 := β]) : ∀ (x : α) (y : β), x
(K α β x y = x : α)

-- Contradiction?
(K α β x y : K₀[?1 := α, ?2 := β].body = (x : α)) → (K α β x y : x)

(K (Type m) (Type n) α β : K₀[?1 := (Type m), ?2 := (Type n)]) →
  (K (Type m) (Type n) α β : ∀ (α : Type m) (β : Type n), α)
```

How are variables in `K₀` typed? Clearly ?1 refers to a free variable.

```
K₀ = ∀ (x : α) (y : β), x
```

where `α` and `β` are free. Clearly, the metavariable `α` is bound in:

```
(λ (α : Type) (β : Type) (k : Ty[K₀] = ?).K₀[?1 := α, ?2 := β])
```

Interestingly, `K₀` seems to imply a typing judgement.

```
(K₀ : ?) = ∀ (x : α) (y : β), α
(S₀ : ?) = ∀ (x : α → β → γ) (y : α → β) (z : α), γ
```

```
(K₁ : ∀ α β, K₀)
(K₁ ℕ ℝ : K₀[α := ℕ, β := ℝ]) x y = x
(S₁ : ∀ α β γ, S₀) x y z = x z (y z)
```

Example: dependent `Vector`.

In λ-calculus first:

```
def ℕ := ∀ (T : Type), (T → T) → T → T
def zero : ℕ := λ T f x, x
def succ : ℕ → ℕ := ∀ n T f x, f (n T f x)
```

In the SK combinators:

```
-- Explicit typings omitted, will do that later
def id := S K K
def mk_id : ∀ t, t → t := S (K₁ : ∀ α β, K₀) (K₁ : ∀ α β, K₀)
def mk_id : ∀ t, t → t := S (K₁ : ∀ α β, K₀) (K₁ : ∀ α β, K₀)
mk_id ℕ = S K₁ K₁ ℕ = K₁ ℕ (K₁ ℕ) = (K₁ ℕ (K₁ ℕ) : K₀[α := ℕ]) = (K₁ ℕ _ : ∀ (x : ℕ) (y : _), ℕ)
-- wrong
-- right
mk_id ℕ = (K₁ ℕ _ _ : ∀ (y : ℕ), ℕ) = S (S K₁ K₁) (S K₁ K₁) ℕ = (S K₁ K₁) ℕ ((S K₁ K₁) ℕ) = (K₁ ℕ (K₁ ℕ) (K₁ ℕ (K₁ ℕ))) = ((K₁ ℕ (K₁ ℕ)) : ∀ (y : (K₁ ℕ)), ℕ
(K₁ ℕ ℕ) : ∀ (y : ℕ), ℕ
mk_id' : ∀ t, t → t = S (S K₁ K₁) (S K₁ K₁ (Type) (Type)) ℕ

-- S copies argument, S x y z = xz (yz)
-- we want mk_id to produce something of type t → t
-- t → t obviously = ∀ (x : t), t
-- We can construct t → t as such K₀[α := t, ̱β := t] t inside an application
-- example:
(K₁ α α α : ∀ (y : α), α)
-- Need to copy α twice
S K (SKS) α = K α α
-- Extend this:
K (Type) (Type) α
S K (SKS) Type = K Type Type

def mk_id := S K (SKS)

K₁ α ̱α _ : ∀ (y : α), α
-- ^ this is what we want

K₁ α ̱β : ∀ (x : α) (y : α), α
-- How do we find something to inhabit α?
-- SKS is the identity function, intuitively it should be of type α → α
-- How do we encode it?
-- Can we simplify K?
K₁ α β ? : ∀ (y : α), α
-- metavariables?

def mk_id := S K (SKS) α

mk_id α = S K₁ α = K₁ α
β

def mk_id' : ∀ t, t → t := 
def t_map := S₁ id 
def ℕ := ∀ (T : Type), (T → T) → T → T
def zero :

-- Where ?1 is a free variable
-- and ?2 is a free variable
def K₀ := ∀ (α : Type) (̱β : Type) (x : α) (y : β̱), α
def (K₁ : K₀) α ̱β x y = x
def S₀ := ∀ (α : Type) (̱β : Type) (γ : Type) (x : α → ̱β → γ) (y : α → β) (z : α), γ
def (S₁ : S₀) α β γ x y z = x z (y z)
def Pi : ∀ (x : Type) (B : Type → Type), B x := sorry
Pi ℕ id = (? : K₀[α := B x, β := _
```

-/

sorry
