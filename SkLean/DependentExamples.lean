/-
# Examples of Dependent Types using Definitions

## Combinator Definitions

-/

def K₀ := ∀ (α : Type) (β : Type) (x : α) (y : β), α
def K₁ : K₀ := fun _α _β x y => x
def S₀ := ∀ (α : Type) (β : Type) (γ : Type) (x : α → β → γ) (y : α → β) (z : α), γ
def S₁ : S₀ := fun α β γ x y z => x z (y z)
def I₀ := ∀ (α : Type) (x : α), α
def I₁ : I₀ := fun (α : Type) (x : α) => x
