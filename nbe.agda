module NBE where

open import Agda.Builtin.String using (String)
open import SystemT hiding (⟦Ty⟧)

-- NbE algorithm (system T with neutral terms)

-- TODO: quantify over a context Γ
data _⊢_⇇_ : Γ → Term → Ty → Set -- Normal terms
data _⊢_⇉_ : Γ → Term → Ty → Set -- Neutral terms

data _⊢_⇇_ where
  nzero : ∀ {Γ : Γ}
        → Γ ⊢ zero ⇇ nat

  nsuc : ∀ {Γ : Γ} (n : Term)
       → Γ ⊢ n ⇇ nat
       → Γ ⊢ suc n ⇇ nat ⇒ nat

  -- abstraction
  nabs : ∀ {Γ : Γ} {S T : Ty} {v : Term}
       → Γ ⊢ v ⇇ T
        -----------
       → Γ ⊢ ƛ v ⇇ S ⇒ T

  -- neutral term
  neutral : ∀ {Γ : Γ} {T : Ty} {𝓊 : Term}
          → Γ ⊢ 𝓊 ⇉ T
            ---------
          → Γ ⊢ 𝓊 ⇇ T

infix 9 _⊢_⇇_

data _⊢_⇉_ where
  -- application on an unknown function
  uapp : ∀ {Γ : Γ} {S T : Ty} {𝓊 v : Term}
       → Γ ⊢ 𝓊 ⇉ S ⇒ T
       → Γ ⊢ v ⇇ S
        --------------
       → Γ ⊢ 𝓊 · v ⇉ T

  -- a variable
  uvar : ∀ {Γ : Γ} {T : Ty} {x : String}
       → ⟨ x ꞉ T ⟩∈ Γ
         -------------
       → Γ ⊢ var x ⇉ T

  -- blocked recursion
  urec : ∀ {Γ : Γ} {T : Ty} {z s 𝓊 : Term}
       → Γ ⊢ z ⇇ T
       → Γ ⊢ s ⇇ nat ⇒ T ⇒ T
       → Γ ⊢ 𝓊 ⇉ nat
         -------------------
       → Γ ⊢ rec z s 𝓊 ⇉ T

infix 9 _⊢_⇉_

-- For the below algorithm to work, Nfᵀ and Neᵀ need to be reintroduced
-- as liftable terms as specified in 2.5. These should be constructed so
-- that a normal/neutral typing judgement can be reused for any context
-- Γ (with the caveat that a Neᵀ could produce ⊥)

{-
instance
  ⟦Ty⟧ : Denotation Ty
  Denotation.⟦ ⟦Ty⟧ ⟧ nat = Nfᵀ nat
  Denotation.⟦ ⟦Ty⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧

↑ᵀ : {T : Ty} → Neᵀ T → ⟦ T ⟧ -- Reflection
↓ᵀ : {T : Ty} → ⟦ T ⟧ → Nfᵀ T -- Reification

↑ᵀ {nat} (neutral 𝓊)     = normal (neutral 𝓊)
↑ᵀ {S ⇒ T} (neutral 𝓊) a with ↓ᵀ a
...                         | normal v = ↑ᵀ (neutral (uapp 𝓊 v))

↓ᵀ {nat} v   = v
↓ᵀ {S ⇒ T} f = nabs lambda where
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
