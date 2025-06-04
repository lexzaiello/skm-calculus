/-
# SK Universes

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

This judgement intuitively holds (a la Calculus of Constructions). Proof irrelevance?
Free variable? Type of `x` changes depending on context (a la metavariable)?

```
K_t = ∀ (x : α) (y : α), x
K_t : ?1
K_t[x := Nat, y : Real] = ∀ (x : Nat) (y : Real), Nat
(K_t[x := Nat, y : Real] : Nat)
```

```
K₀ : ∀ x : ?1, y : ?2, ?1
```

How are variables brought into scope?

```
(K₁ : K₀[?1 := α, ?2 := β]) α β x y = x

K₀ : α = ∀ ?1 ?2 (α : ?1) (β : ?2), α

K₁ : K₀ = λ α β (x : α) (y : β).x
K₁ : ∀ ?1 ?2 (α : ?1) (β : ?2), α = λ ?1 ?2 (x : ?1) (y : ?2).x
```

Clearly, this judgement is true:

```
K₁ Nat Real 1 2 → K₀[?1 := Nat, ?2 := Real, α := 1, β := 2] → K₁ Nat Real 1 2:

K₀ : α = ∀ ?1 ?2 (α : ?1) (β : ?2), α
(K₁ : K₀) α β x y = x
```

Substitution is a shared behavior of `∀` and `λ`. `∀` is typeable, `λ` is computable, then:

```
(K₂ : K₁)
```

-/

def S₀ (α : Type) (β : Type) (γ : Type) : (α → β → γ) → (α → β) → α → γ :=
  fun x y z => x z (y z)

def K_sub_huh := S₀ 
