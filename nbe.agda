module NBE where

open import Agda.Builtin.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import SystemT using (Ty; Γ; Denotation; nat; _⇒_; _∋_; _,_; ⟦_⟧)

-- NbE algorithm (system T with neutral terms)

data Neᵀ {T : Ty} (Γ : Γ) : Set -- Neutral terms
data Nfᵀ (Γ : Γ) : {T : Ty} → Set -- Normal terms

data Neᵀ {T} Γ where
  -- application on an unknown function
  app : ∀ {S : Ty}
      → Neᵀ {S ⇒ T} Γ
      → Nfᵀ Γ {S}
        -------------
      → Neᵀ {T} Γ

  -- a variable
  var : (x : Γ ∋ T)
        -----------
      → Neᵀ {T} Γ

  -- blocked recursion
  rec : Nfᵀ Γ {T}
      → Nfᵀ Γ {nat ⇒ T ⇒ T}
      → Neᵀ {nat} Γ
        -----------------
      → Neᵀ {T} Γ

--syntax Neᵀ Γ {T} t = Γ ⊢ t ⇉ T

data Nfᵀ Γ where
  nzero : Nfᵀ Γ {nat}

  nsuc : Nfᵀ Γ {nat}
       → Nfᵀ Γ {nat}

  -- abstraction
  abs : ∀ {S T : Ty}
      → Nfᵀ (Γ , S) {T}
        -------------
      → Nfᵀ Γ {S ⇒ T}

  -- neutral term
  neutral : ∀ {T : Ty}
          → Neᵀ {T} Γ
            -------
          → Nfᵀ Γ {T}

data Nf (T : Ty) : Set where
  nf : ∀ (Γ : Γ) → Nfᵀ Γ {T} → Nf T

data Ne (T : Ty) : Set where
  ne : ∀ (Γ : Γ) → Neᵀ {T} Γ → Ne T
  ⊥  : Ne T

data ℕ : Set where
  ne   : Ne nat → ℕ
  zero : ℕ
  suc  : ℕ → ℕ

instance
    ⟦Ty⟧ : Denotation Ty
    Denotation.⟦ ⟦Ty⟧ ⟧ nat = ℕ
    Denotation.⟦ ⟦Ty⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧

↑ᵀ : {T : Ty} → Ne T → ⟦ T ⟧
↑ᵀ {nat} 𝓊̂ = ne 𝓊̂
↑ᵀ {S ⇒ T} (ne Γ₁ x) v = {!!}
↑ᵀ {S ⇒ T} ⊥ v = {!!}

↓ᵀ : {T : Ty} → ⟦ T ⟧ → Nf T
↓ᵀ = {!!}

-- Liftable terms must be reintroduced for the below algorithm (formerly
-- an implementation of the "sketch" in 2.3 can) to work


{-

↑ᵀ : {T : Ty} → Neᵀ T → ⟦ T ⟧ -- Reflection
↓ᵀ : {T : Ty} → ⟦ T ⟧ → Nfᵀ T -- Reification

↑ᵀ = ?
↓ᵀ = ?

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

-}
