module NBE where

open import Denotation using (Ty; nat; _arrow_)

-- NbE algorithm (system T with neutral terms)

-- TODO: quantify over a context Γ
data Neᵀ : ∀ (T : Ty) → Set
data Nfᵀ : ∀ (T : Ty) → Set

data Neᵀ where
  app : ∀ {S T : Ty} → (u : Neᵀ (S arrow T)) → (v : Nfᵀ S) → Neᵀ T

data Nfᵀ where
  z : Nfᵀ nat
  suc : Nfᵀ nat → Nfᵀ nat
  func : ∀ {S T : Ty} → (v : Nfᵀ T) → Nfᵀ (S arrow T)
  unknown : ∀ {T : Ty} → Neᵀ T → Nfᵀ T


record ↑ᵀ {T : Ty} : Set where
  field
    reflect : Neᵀ T → Nfᵀ T

↑ᴺ : ↑ᵀ {nat}
↑ᴺ = record { reflect = λ u → unknown u }

{-
record ↓ᴳ {T : Set} : Set₁ where
  field
    reify : ⟦ T ⟧ → Nfᵀ T
-}

