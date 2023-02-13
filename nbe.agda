module NBE where

open import Agda.Builtin.String using (String)
open import SystemT hiding (⟦Ty⟧)

-- NbE algorithm (system T with neutral terms)

data Neᵀ (Γ : Γ) : ∀ {T : Ty} → Γ ⊢ T → Set -- Neutral terms
data Nfᵀ (Γ : Γ) : ∀ {T : Ty} → Γ ⊢ T → Set -- Normal terms

data Neᵀ Γ where
  -- application on an unknown function
  app : ∀ {S T : Ty} {𝓊 : Γ ⊢ S ⇒ T} {v : Γ ⊢ S}
      → Neᵀ Γ 𝓊
      → Nfᵀ Γ v
        -------------
      → Neᵀ Γ (𝓊 · v)

  -- a variable
  var : ∀ {T : Ty}
      → (x : Γ ∋ T)
        -----------
      → Neᵀ Γ (` x)

  -- blocked recursion
  rec : ∀ {T : Ty} {z : Γ ⊢ T} {s : Γ ⊢ nat ⇒ T ⇒ T} {𝓊 : Γ ⊢ nat}
      → Nfᵀ Γ z
      → Nfᵀ Γ s
      → Neᵀ Γ 𝓊
        -----------------
      → Neᵀ Γ (rec z s 𝓊)

syntax Neᵀ Γ {T} t = Γ ⊢ t ⇉ T

data Nfᵀ Γ where
  nzero : Nfᵀ Γ zero

  nsuc : ∀ {v : Γ ⊢ nat}
       → Nfᵀ Γ v
       → Nfᵀ Γ (suc v)

  -- abstraction
  abs : ∀ {S T : Ty} {f : Γ ⊢ S ⇒ T}
        -------
      → Nfᵀ Γ f

  -- neutral term
  neutral : ∀ {T : Ty} {𝓊 : Γ ⊢ T}
          → Neᵀ Γ 𝓊
            -------
          → Nfᵀ Γ 𝓊

syntax Nfᵀ Γ {T} t = Γ ⊢ t ⇇ T

-- Liftable terms must be reintroduced for the below algorithm (formerly
-- an implementation of the "sketch" in 2.3 can) to work

{-

⟦Ty⟧ : (T : Ty) → ∀ (Γ : Γ) → Set
⟦Ty⟧ nat = ∀ (Γ : Γ) → Nfᵀ Γ (Γ ⊢ nat)
⟦Ty⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧

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

-}
