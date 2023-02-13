module NBE where

open import Agda.Builtin.String using (String)
open import SystemT using (Ty; nat; _⇒_; Γ; Denotation; ⟦_⟧)

-- NbE algorithm (system T with neutral terms)

-- TODO: quantify over a context Γ (section 2.5)
data Neᵀ : ∀ (T : Ty) → Set -- Neutral terms
data Nfᵀ : ∀ (T : Ty) → Set -- Normal terms

data Neᵀ where
  -- application on an unknown function
  app : ∀ {S T : Ty}
      → (𝓊 : Neᵀ (S ⇒ T))
      → (v : Nfᵀ S)
        -----------------
      → Neᵀ T

  -- a variable
  var : ∀ {T}
      → String
        ------
      → Neᵀ T

  -- blocked recursion
  rec : ∀ {T : Ty}
      → (z↓ : Nfᵀ T)
      → (s↓ : Nfᵀ (nat ⇒ T ⇒ T))
      → (𝓊 : Neᵀ nat)
        ------------------------
      → Neᵀ T

data Nfᵀ where
  zero : Nfᵀ nat

  suc : Nfᵀ nat → Nfᵀ nat

  -- abstraction
  abs : ∀ {S T : Ty}
      → (f : String → Nfᵀ T)
        --------------------
      → Nfᵀ (S ⇒ T)

  -- neutral term
  neutral : ∀ {T : Ty}
    → (𝓊 : Neᵀ T)
      -----------
    → Nfᵀ T

instance
  ⟦Ty⟧ : Denotation Ty
  Denotation.⟦ ⟦Ty⟧ ⟧ nat = Nfᵀ nat
  Denotation.⟦ ⟦Ty⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧

↑ᵀ : {T : Ty} → Neᵀ T → ⟦ T ⟧ -- Reflection
↓ᵀ : {T : Ty} → ⟦ T ⟧ → Nfᵀ T -- Reification

↑ᵀ {nat} 𝓊     = neutral 𝓊
↑ᵀ {S ⇒ T} 𝓊 a = ↑ᵀ (app 𝓊 v) where v = ↓ᵀ a

↓ᵀ {nat} v   = v
↓ᵀ {S ⇒ T} f = abs lambda where
  lambda : String → Nfᵀ T
  -- TODO: freshness of x
  lambda x =  ↓ᵀ (f a) where a = ↑ᵀ (var x)

-- TODO: the original habilitation has the type of the first
-- argument to rec as "N" (nat), this seems to be a typo
ml-rec : ∀ {T : Ty} → ⟦ T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T ⟧
ml-rec z s zero            = z
ml-rec z s (suc v)         = s v (ml-rec z s v)
ml-rec {T} z s (neutral 𝓊) = ↑ᵀ (rec z↓ s↓ 𝓊) where
  z↓ = ↓ᵀ {T} z
  s↓ = ↓ᵀ {nat ⇒ T ⇒ T} s
