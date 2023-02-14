module NbE where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import SystemT hiding (⟦Type⟧)

{- Section 2.3 -- System T with neutral and normal terms -}

data Ne (T : Type) (Γ : Γ) : Set -- Neutral terms
data Nf : Type → Γ → Set         -- Normal terms

data Ne T Γ where
  -- application on an unknown function
  _·_ : ∀ {S : Type}
      → Ne (S ⇒ T) Γ
      → Nf S Γ
        ------------
      → Ne T Γ

  -- a variable
  `_ : (x : Γ ∋ T)
       -----------
     → Ne T Γ

  -- blocked recursion
  rec : Nf T Γ
      → Nf (nat ⇒ T ⇒ T) Γ
      → Ne nat Γ
        ------------------
      → Ne T Γ

data Nf where
  zero : ∀ {Γ : Γ} → Nf nat Γ

  suc : ∀ {Γ : Γ}
      → Nf nat Γ
        --------
      → Nf nat Γ

  -- abstraction
  ƛ : ∀ {S T : Type} {Γ : Γ}
    → Nf T (Γ , S)
      ------------
    → Nf (S ⇒ T) Γ

  -- neutral term
  neutral : ∀ {T : Type} {Γ : Γ}
          → Ne T Γ
            -----------
          → Nf T Γ

{- Section 2.5 -- liftable terms, updated NbE algorithm -}

-- Liftable neutral term
data Ne↑ (T : Type) : Set where
  ne↑ : (∀ (Γ : Γ) → Ne T Γ ⊎ ⊤) → Ne↑ T

-- Liftable normal term
data Nf↑ (T : Type) : Set where
  nf↑ : (∀ (Γ : Γ) → Nf T Γ) → Nf↑ T

-- Interpretation of type nat: naturals with embedded
-- liftable neutrals
data ℕ̂ : Set where
  zero : ℕ̂
  suc : ℕ̂ → ℕ̂
  ne : Ne↑ nat → ℕ̂

instance
  ⟦Type⟧ : Denotation Type
  Denotation.⟦ ⟦Type⟧ ⟧ nat = ℕ̂
  Denotation.⟦ ⟦Type⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧

-- Reflection of neutral terms of type T into
-- semantic objects in ⟦T⟧
↑ᵀ : {T : Type} → Ne↑ T → ⟦ T ⟧

-- Reification of semantic objects in ⟦T⟧ into
-- normal terms of type T
↓ᵀ : {T : Type} → ⟦ T ⟧ → Nf↑ T -- Reification

-- ↑ᴺ - Reflection of neutral terms of type nat into ℕ̂,
--      here we just embed the liftable neutral
↑ᵀ {nat} 𝓊̂ = ne 𝓊̂

-- ↑ˢ⃗ᵗ - Reflection of neutral terms of type S → T,
--        into ⟦S⟧ → ⟦T⟧. We reify a semantic object in ⟦S⟧
--        and then reflect the neutral term resulting from the
--        application of the reified object to the original
--        neutral term
↑ᵀ {S ⇒ T} (ne↑ 𝓊↑) a with ↓ᵀ a
...  | nf↑ v↑ = ↑ᵀ (ne↑ 𝓊·v↑) where
  𝓊·v↑ : ∀ (Γ : Γ) → Ne T Γ ⊎ ⊤
  𝓊·v↑ Γ with 𝓊↑ Γ | v↑ Γ
  ... | inj₁ 𝓊     | v = inj₁ (𝓊 · v)
  ... | inj₂ tt    | _ = inj₂ tt

-- Create a new lifted variable of type S in the context Γ,
-- which can only be applied to extensions of Γ , S
mk-lifted-var : ∀ {S : Type} (Γ : Γ) → Ne↑ S
mk-lifted-var {S} Γ = ne↑ var↑ where
  var↑ : ∀ (Γ′ : SystemT.Γ) → Ne S Γ′ ⊎ ⊤
  var↑ Γ′ with Γ′ Γ-extension? (Γ , S)
  ... | yes pf  = inj₁ (` (lookup-extension pf `Z))
  ... | no _    = inj₂ tt

-- ↓ᴺ - Reification of semantic objects of type ⟦N⟧, which
--      are our naturals with embedded liftable neutrals (ℕ̂).
--      For the interesting case of embedded liftable neutrals,
--      zero is used if the neutral cannot be lifted to the
--      context Γ
↓ᵀ {nat} = ↓ℕ̂ where
  ↓ℕ̂ : ⟦ nat ⟧ → Nf↑ nat
  ↓ℕ̂ zero = nf↑ (λ _ → zero)
  ↓ℕ̂ (suc n) with ↓ℕ̂ n
  ... | nf↑ n↑ = nf↑ (λ Γ → suc (n↑ Γ))
  ↓ℕ̂ (ne (ne↑ 𝓊↑)) = nf↑ 𝓊̂ where
    𝓊̂ : ∀ (Γ : Γ) → Nf nat Γ
    𝓊̂ Γ with 𝓊↑ Γ
    ... | inj₁ 𝓊  = neutral 𝓊
    ... | inj₂ tt = zero

-- ↓ˢ⃗ᵗ - Reification of semantic objects of type ⟦S → T⟧,
--        which are functions of type (⟦S⟧ → ⟦T⟧). The
--        resulting normal term is an abstraction over
--        the reification of the function applied to the
--        reflection of the bound variable
↓ᵀ {S ⇒ T} f = nf↑ f↑ where
  f↑ : ∀ (Γ : Γ) → Nf (S ⇒ T) Γ
  f↑ Γ with ↓ᵀ (f a) where a = ↑ᵀ (mk-lifted-var Γ)
  ... | nf↑ f·a↑ = ƛ (f·a↑ (Γ , S))

{-
-- TODO: the original habilitation has the type of the first
-- argument to rec as "N" (nat), this seems to be a typo
ml-rec : ∀ {T : Type} → ⟦ T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T ⟧
ml-rec z s zero            = z
ml-rec z s (suc v)         = s v (ml-rec z s v)
ml-rec {T} z s (neutral 𝓊) = ↑ᵀ (rec z↓ s↓ 𝓊) where
  z↓ = ↓ᵀ {T} z
  s↓ = ↓ᵀ {nat ⇒ T ⇒ T} s
-}
