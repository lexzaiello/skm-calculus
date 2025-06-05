/-
# Examples of Dependent Types using Definitions

## Combinator Definitions

-/

import Mathlib.Tactic

abbrev K₀.{m, n} := ∀ (α : Type m) (β : Type n) (_x : α) (_y : β), α
def K₁ : K₀ := fun _α _β x _y => x

abbrev S₀.{m, n, o} := ∀ (α : Type m) (β : Type n) (γ : Type o) (_x : α → β → γ) (_y : α → β) (_z : α), γ
def S₁ : S₀ := fun _α _β _γ x y z => x z (y z)

/-
## Π type derivation:

I denote `_` to mean a hole filled by the typing context.
I denote `S` and `K` to mean `S₁ _ _ _` and `K₁ _ _`.

```
def flip := S (S (K (S (K S) K))) (K (S K K))
def Π₁ (α : Type) (t_map : Type → Type) : t_map α := flip

Π₁ ℕ id = id ℕ = ℕ
```
-/

