module NBE where

open import Agda.Builtin.String using (String)
open import Denotation using (Ty; nat; _arrow_)

-- NbE algorithm (system T with neutral terms)

-- TODO: quantify over a context Γ
data Neᵀ : ∀ (T : Ty) → Set
data Nfᵀ : ∀ (T : Ty) → Set

data Neᵀ where
  app : ∀ {S T : Ty} → (u : Neᵀ (S arrow T)) → (v : Nfᵀ S) → Neᵀ T
  var : ∀ {T} → String → Neᵀ T

data Nfᵀ where
  z : Nfᵀ nat
  suc : Nfᵀ nat → Nfᵀ nat
  func : ∀ {S T : Ty} → (f : String → Nfᵀ T) → Nfᵀ (S arrow T)
  unknown : ∀ {T : Ty} → Neᵀ T → Nfᵀ T

⟦_⟧ : Ty → Set
⟦ nat ⟧ = Nfᵀ nat
⟦ S arrow T ⟧ = ⟦ S ⟧ → ⟦ T ⟧

↑ᵀ : {T : Ty} → Neᵀ T → ⟦ T ⟧
↓ᵀ : {T : Ty} → ⟦ T ⟧ → Nfᵀ T

↑ᵀ {nat} u = unknown u
↑ᵀ {S arrow T} u a = ↑ᵀ (app u v) where v = ↓ᵀ a

↓ᵀ {nat} v = v
↓ᵀ {S arrow T} f = func lambda where
  lambda : String → Nfᵀ T
  -- TODO: freshness of x
  lambda x =  ↓ᵀ (f a) where a = ↑ᵀ (var x)
