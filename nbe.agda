module NBE where



-- NbE algorithm (system T with neutral terms)

data Neᵀ : (T : Set) → Set where


record ⟦_⟧′ (T : Set) : Set₁ where
  field
    denote : (x : T) → Set

record ↑ᵀ {T T′ : Set} : Set₁ where
  field
    reflect : Neᵀ T → ⟦ T ⟧′

record ↓ᴳ : Set where

