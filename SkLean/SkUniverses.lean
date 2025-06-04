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

This judgement intuitively holds (a la Calculus of Constructions)
Free variable? Type of `x` changes depending on context (a la metavariable)?

```
K_t = ∀ (x : (.var 3)) (y : (.var 3₁)), x
K_t : ?1
K_thing = ∀ α : Type, β : Type, K_t
K_thing[α := ℕ, β := ℝ] → K_thing = ∀ (x : α) (y : β), (x : α)
K_thing : (x : α)
```

We can say that `K_t` is only well-typed under a context Γ where `x : something ∧ y : something₂`.

However, to define the `K` combinator, we need some way to instantiate `(.var 3) and (.var 3₁)` at the expression level.

```
((K α β) : K₀[(.var 3) := α, (.var 3₂) := β]) : ∀ (x : α) (y : β), x
(K α β x y = x : α)
(K α β x y : K₀[(.var 3) := α, (.var 3₂) := β].body = (x : α)) → (K α β x y : x)
```

Contradiction?

```
(K (Type m) (Type n) α β : K₀[(.var 3) := (Type m), (.var 3₂) := (Type n)]) → (K (Type m) (Type n) α β : ∀ (α : Type m) (β : Type n), α)
(K α β x y : α) = (x : α)
```

Seems like a valid judgement.
-/

#check Fin

def S₀ (α : Type) (β : Type) (γ : Type) : (α → β → γ) → (α → β) → α → γ :=
  fun x y z => x z (y z)

def K_sub_huh := S₀ 
