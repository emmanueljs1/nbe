module NBE where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import SystemT hiding (⟦Ty⟧)

{- Section 2.3 -- System T with neutral and normal terms -}

data Neᵀ (Γ : Γ) (T : Ty) : Set -- Neutral terms
data Nfᵀ (Γ : Γ) : Ty → Set     -- Normal terms

data Neᵀ Γ T where
  -- application on an unknown function
  _·_ : ∀ {S : Ty}
      → Neᵀ Γ (S ⇒ T)
      → Nfᵀ Γ S
        -------------
      → Neᵀ Γ T

  -- a variable
  `_ : (x : Γ ∋ T)
       -----------
     → Neᵀ Γ T

  -- blocked recursion
  rec : Nfᵀ Γ T
      → Nfᵀ Γ (nat ⇒ T ⇒ T)
      → Neᵀ Γ nat
        ------------------
      → Neᵀ Γ T

data Nfᵀ Γ where
  zero : Nfᵀ Γ nat

  suc : Nfᵀ Γ nat
        ---------
      → Nfᵀ Γ nat

  -- abstraction
  ƛ : ∀ {S T : Ty}
    → Nfᵀ (Γ , S) T
      -------------
    → Nfᵀ Γ (S ⇒ T)

  -- neutral term
  neutral : ∀ {T : Ty}
          → Neᵀ Γ T
            -------
          → Nfᵀ Γ T

{- Section 2.5 -- liftable terms, updated NbE algorithm -}

-- Liftable neutral term
data Ne (T : Ty) : Set where
  ne : (∀ (Γ : Γ) → Neᵀ Γ T ⊎ ⊤) → Ne T

-- Liftable normal term
data Nf (T : Ty) : Set where
  nf : (∀ (Γ : Γ) → Nfᵀ Γ T) → Nf T

-- Denotation of type nat with embedded liftable neutrals
data ℕ̂ : Set where
  zero : ℕ̂
  suc : ℕ̂ → ℕ̂
  ne : Ne nat → ℕ̂

instance
  ⟦Ty⟧ : Denotation Ty
  Denotation.⟦ ⟦Ty⟧ ⟧ nat = ℕ̂
  Denotation.⟦ ⟦Ty⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧

↑ᵀ : {T : Ty} → Ne T → ⟦ T ⟧ -- Reflection
↓ᵀ : {T : Ty} → ⟦ T ⟧ → Nf T -- Reification

↑ᵀ {nat} 𝓊̂@(ne _) = ne 𝓊̂
↑ᵀ {S ⇒ T} (ne u↑) a with ↓ᵀ a
...  | nf v↑ = ↑ᵀ (ne uv) where
  uv : ∀ (Γ : Γ) → Neᵀ Γ T ⊎ ⊤
  uv Γ with u↑ Γ | v↑ Γ
  ... | inj₁ 𝓊   | v = inj₁ (𝓊 · v)
  ... | inj₂ tt  | _ = inj₂ tt

-- Reification of a nat
↓ℕ̂ : ℕ̂ → Nf nat
↓ℕ̂ zero = nf (λ _ → zero)
↓ℕ̂ (suc n) with ↓ℕ̂ n
...           | nf n↑ = nf (λ Γ → suc (n↑ Γ))
↓ℕ̂ (ne (ne u↑)) = nf ûΓ where
  ûΓ : ∀ (Γ : Γ) → Nfᵀ Γ nat
  ûΓ Γ with u↑ Γ
  ... | inj₁ 𝓊 = neutral 𝓊
  ... | inj₂ tt = zero

-- lift a var in context gamma (i.e. "pick fresh")
liftvar : ∀ {S : Ty} → Γ → Ne S
liftvar {S} Γ = ne var↑ where
  var↑ : ∀ (Γ′ : SystemT.Γ) → Neᵀ Γ′ S ⊎ ⊤
  var↑ Γ′ = {!!}

↓ᵀ {nat} = ↓ℕ̂
↓ᵀ {S ⇒ T} f = nf f↑ where
  f↑ : ∀ (Γ : Γ) → Nfᵀ Γ (S ⇒ T)
  f↑ Γ with ↑ᵀ (liftvar Γ)
  ...  | a
       with ↓ᵀ (f a)
  ...  | nf f·a↑ = ƛ (f·a↑ (Γ , S))

{-
-- TODO: the original habilitation has the type of the first
-- argument to rec as "N" (nat), this seems to be a typo
ml-rec : ∀ {T : Ty} → ⟦ T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T ⟧
ml-rec z s zero            = z
ml-rec z s (suc v)         = s v (ml-rec z s v)
ml-rec {T} z s (neutral 𝓊) = ↑ᵀ (rec z↓ s↓ 𝓊) where
  z↓ = ↓ᵀ {T} z
  s↓ = ↓ᵀ {nat ⇒ T ⇒ T} s
-}
