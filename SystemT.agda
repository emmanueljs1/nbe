module SystemT where

open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

{- Section 2.1 -- Basic system T -}

-- Types in the language
data Type : Set where
  nat : Type
  _⇒_ : ∀ (S T : Type) → Type

infixr 7 _⇒_

-- Typing contexts
data Γ : Set where
  ∅ : Γ
  _,_ : Γ → Type → Γ

infixl 5 _,_

-- Lookup judgement for contexts
-- (corresponds to de Brujin indices)
data _∋_ : Γ → Type → Set where
  `Z : ∀ {Γ : Γ} {T : Type}
        ---------
      → Γ , T ∋ T

  `S_ : ∀ {Γ : Γ} {S T : Type}
      → Γ ∋ T
        ---------
      → Γ , S ∋ T

infix 4 _∋_

-- Typing judgement in a context
-- (these correspond to intrinsically typed terms)
data _⊢_ (Γ : Γ) : Type → Set where
  zero : Γ ⊢ nat

  suc : Γ ⊢ nat ⇒ nat

  rec  : ∀ {T : Type}
         ---------------------------------
       → Γ ⊢ (T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T)

  `_ : ∀ {S : Type}
     → Γ ∋ S
       -----
     → Γ ⊢ S

  ƛ_ : ∀ {S T : Type}
     → Γ , S ⊢ T
       ---------
     → Γ ⊢ S ⇒ T

  _·_ : ∀ {S T : Type}
      → Γ ⊢ S ⇒ T
      → Γ ⊢ S
        ---------
      → Γ ⊢ T

infix 4 _⊢_
infix 5 ƛ_
infixl 7 _·_
infix 9 `_

-- We use the following record to represent interpretations
-- of types and contexts in System T. This will help
-- with the many definitions in the NbE algorithm.
--
-- The original interpretations of types (and of lookup and
-- typing judgements, which are defined independently as
-- functions) are left out, as they need to be updated to
-- work with the final NbE algorithm.
record Denotation (D : Set) : Set₁ where
  field
    ⟦_⟧ : D → Set

open Denotation {{...}} public

instance
    -- The denotation of a context Γ, generalized over
    -- any denotation to be used with the more NbE
    -- specific denotation of types introduced in
    -- later sections
    ⟦Γ⟧ : {{_ : Denotation Type}} → Denotation Γ
    Denotation.⟦ ⟦Γ⟧ ⟧ ∅ = ⊤
    Denotation.⟦ ⟦Γ⟧ ⟧ (Γ , T) = ⟦ Γ ⟧ × ⟦ T ⟧

{- Section 2.3 -- System T with neutral and normal terms -}

data Ne (T : Type) (Γ : Γ) : Γ ⊢ T → Set     -- Neutral terms
data Nf : (T : Type) → (Γ : Γ) → Γ ⊢ T → Set -- Normal terms

data Ne T Γ where
  -- application on an unknown function
  ne-app : ∀ {S : Type} {𝓊 : Γ ⊢ S ⇒ T} {𝓋 : Γ ⊢ S}
         → Ne (S ⇒ T) Γ 𝓊
         → Nf S Γ 𝓋
           --------------
         → Ne T Γ (𝓊 · 𝓋)

  -- a variable is always blocked
  ne-var : (x : Γ ∋ T)
           ------------
         → Ne T Γ (` x)

  -- recursion blocked on an unknown natural
  ne-rec : {𝓋z : Γ ⊢ T} {𝓋s : Γ ⊢ nat ⇒ T ⇒ T} {𝓊 : Γ ⊢ nat}
         → Nf T Γ 𝓋z
         → Nf (nat ⇒ T ⇒ T) Γ 𝓋s
         → Ne nat Γ 𝓊
           --------------------------
         → Ne T Γ (rec · 𝓋z · 𝓋s · 𝓊)

data Nf where
  -- zero is a normal term
  nf-zero : ∀ {Γ : Γ} → Nf nat Γ zero

  -- suc applied to a normal term is a normal term
  nf-suc : ∀ {Γ : Γ} {𝓋 : Γ ⊢ nat}
         → Nf nat Γ 𝓋
           ------------------
         → Nf nat Γ (suc · 𝓋)

  -- abstraction over a normal term is a normal term
  nf-abs : ∀ {S T : Type} {Γ : Γ} {𝓋 : Γ , S ⊢ T}
         → Nf T (Γ , S) 𝓋
           ------------------
         → Nf (S ⇒ T) Γ (ƛ 𝓋)

  -- a neutral term is a normal term
  nf-neutral : ∀ {T : Type} {Γ : Γ} {𝓊 : Γ ⊢ T}
             → Ne T Γ 𝓊
               --------
             → Nf T Γ 𝓊

{- Section 2.2 -- normalization, definitional equality -}

-- TODO: define
data _defeq_ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → Γ ⊢ T → Set where

{- Section 2.5 -- liftable terms, updated NbE algorithm -}

-- Liftable neutral term
data Ne↑ (T : Type) : Set where
  ne↑ : (∀ (Γ : Γ) → ((∃[ t ] Ne T Γ t) ⊎ ⊤)) → Ne↑ T

-- Liftable normal term
data Nf↑ (T : Type) : Set where
  nf↑ : (∀ (Γ : Γ) → ∃[ t ] Nf T Γ t) → Nf↑ T

-- Interpretation of type nat: naturals with embedded
-- liftable neutrals
data ℕ̂ : Set where
  zero : ℕ̂
  suc : ℕ̂ → ℕ̂
  ne : Ne↑ nat → ℕ̂

-- Since the interpretation of System T used in NbE is using
-- liftable neutral and normal terms, we instantiate the
-- denotation of types to use the interpretation of type
-- nat with embedded liftable neutrals (instead of the
-- original ℕ in Section 2.1)
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
  𝓊·v↑ : ∀ (Γ : Γ) → (∃[ t ] Ne T Γ t) ⊎ ⊤
  𝓊·v↑ Γ with 𝓊↑ Γ        | v↑ Γ
  ... | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩ | ⟨ 𝓋 , pf-𝓋 ⟩ = inj₁ ⟨ 𝓊 · 𝓋 , ne-app pf-𝓊 pf-𝓋 ⟩
  ... | inj₂ tt           | _ = inj₂ tt

-- Rules for determining when one context is the
-- extension of another.
data _Γ-≤_ : Γ → Γ → Set where
  ∅-≤ : ∀ {Γ : Γ}
        ---------
       → Γ Γ-≤ ∅

  ,-≤ : ∀ {Γ Γ′ : Γ} {T : Type}
      → Γ′ Γ-≤ Γ
        ------------
      → Γ′ , T Γ-≤ Γ

infix 4 _Γ-≤_

_Γ-≤?_ : ∀ (Γ′ Γ : Γ) → Dec (Γ′ Γ-≤ Γ)
∅ Γ-≤? ∅ = yes ∅-≤
∅ Γ-≤? (_ , _) = no λ()
(_ , _) Γ-≤? ∅ = yes ∅-≤
(Γ′ , _) Γ-≤? Γ@(_ , _) with Γ′ Γ-≤? Γ
... | yes pf  = yes (,-≤ pf)
... | no ¬pf  = no λ{ (,-≤ pf) → ¬pf pf }

-- Given one context is an extension of another, and a
-- lookup judgement in the original context, there
-- is a corresponding lookup judgement in the extended context.
lookup-Γ-≤ : ∀ {Γ′ Γ : Γ} {T : Type}
           → Γ′ Γ-≤ Γ
           → Γ ∋ T
             --------
           → Γ′ ∋ T
lookup-Γ-≤ (,-≤ pf) i
  with lookup-Γ-≤ pf i
... | j = `S j

-- Create a new lifted variable of type S in the context Γ,
-- which can only be applied to extensions of Γ , S
mk-lifted-var : ∀ {S : Type} (Γ₁ : Γ) → Ne↑ S
mk-lifted-var {S} Γ₁ = ne↑ var↑ where
  var↑ : ∀ (Γ₂ : Γ) → (∃[ t ] Ne S Γ₂ t) ⊎ ⊤
  var↑ Γ₂ with Γ₂ Γ-≤? (Γ₁ , S)
  ... | yes pf  = inj₁ ⟨ ` x , ne-var x ⟩ where x = lookup-Γ-≤ pf `Z
  ... | no _    = inj₂ tt

-- ↓ᴺ - Reification of semantic objects of type ⟦N⟧, which
--      are our naturals with embedded liftable neutrals (ℕ̂).
--      For the interesting case of embedded liftable neutrals,
--      zero is used if the neutral cannot be lifted to the
--      context Γ
↓ℕ̂ : ⟦ nat ⟧ → Nf↑ nat
↓ℕ̂ zero = nf↑ (λ _ → ⟨ zero , nf-zero ⟩)
↓ℕ̂ (suc n) with ↓ℕ̂ n
... | nf↑ n↑ = nf↑ suc↑ where
  suc↑ : (Γ : Γ) → ∃[ t ] Nf nat Γ t
  suc↑ Γ with n↑ Γ
  ... | ⟨ 𝓋 , pf ⟩ = ⟨ suc · 𝓋 , nf-suc pf ⟩
↓ℕ̂ (ne (ne↑ 𝓊↑)) = nf↑ 𝓊̂ where
  𝓊̂ : ∀ (Γ : Γ) → ∃[ t ] Nf nat Γ t
  𝓊̂ Γ with 𝓊↑ Γ
  ... | inj₁ ⟨ 𝓊 , pf ⟩ = ⟨ 𝓊 , nf-neutral pf ⟩
  ... | inj₂ tt         = ⟨ zero , nf-zero ⟩

↓ᵀ {nat} = ↓ℕ̂

-- ↓ˢ⃗ᵗ - Reification of semantic objects of type ⟦S → T⟧,
--        which are functions of type (⟦S⟧ → ⟦T⟧). The
--        resulting normal term is an abstraction over
--        the reification of the function applied to the
--        reflection of the bound variable
↓ᵀ {S ⇒ T} f = nf↑ f↑ where
  f↑ : ∀ (Γ : Γ) → ∃[ t ] Nf (S ⇒ T) Γ t
  f↑ Γ with ↓ᵀ (f a) where a = ↑ᵀ (mk-lifted-var Γ)
  ... | nf↑ f·a↑
      with f·a↑ (Γ , S)
  ... | ⟨ 𝓋 , pf ⟩ = ⟨ ƛ 𝓋 , nf-abs pf ⟩

-- Reflection of a context gamma
↑Γ : ∀ (Γ : Γ) → ⟦ Γ ⟧
↑Γ ∅ = tt
↑Γ (Γ , T) = ⟨ ↑Γ Γ  , ↑ᵀ {T} (mk-lifted-var Γ) ⟩

-- Denotation of primitive recursion in language,
-- updated in section 2.5 from the basic denotation
-- to handle the new case of recursion being over
-- an embedded liftable neutral by reflecting a
-- "liftable" recursion over a liftable neutral term

-- Note: the original habilitation has the type of the first
-- argument to rec as "N" (nat), this seems to be a typo
⟦rec⟧ : ∀ {T : Type} → ⟦ T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T ⟧
⟦rec⟧ z s zero = z
⟦rec⟧ z s (suc n) = s n (⟦rec⟧ z s n)
⟦rec⟧ {T} z s (ne (ne↑ u↑)) = ↑ᵀ (ne↑ rec↑) where
  rec↑ : ∀ (Γ : Γ) → ∃[ t ] Ne T Γ t ⊎ ⊤
  rec↑ Γ with u↑ Γ
  ... | inj₂ tt = inj₂ tt
  ... | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩
         with ↓ᵀ z | ↓ᵀ s
  ... | nf↑ z↑     | nf↑ s↑
        with z↑ Γ      | s↑ Γ
  ... | ⟨ 𝓋z , pf-𝓋z ⟩ | ⟨ 𝓋s , pf-𝓋s ⟩ = inj₁ ⟨ rec · 𝓋z · 𝓋s · 𝓊 , ne-rec pf-𝓋z pf-𝓋s pf-𝓊 ⟩

-- And the corresponding denotations of the
-- lookup and typing judgements.
--
-- These are not directly shown in section 2.5, but they
-- are very similar to their counterparts in section 2.1

∋⟦_⟧ : ∀ {Γ : Γ} {T : Type} → Γ ∋ T → ⟦ Γ ⟧ → ⟦ T ⟧
∋⟦_⟧ {Γ , T} `Z ⟨ _ , a ⟩ = a
∋⟦_⟧ {Γ , T} (`S x) ⟨ ρ , _ ⟩ = ∋⟦ x ⟧ ρ

⊢⟦_⟧ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → ⟦ Γ ⟧ → ⟦ T ⟧
⊢⟦ zero ⟧ _ = zero
⊢⟦ suc ⟧ _ = suc
⊢⟦ rec ⟧ _ = ⟦rec⟧
⊢⟦ ` x ⟧ = ∋⟦ x ⟧
⊢⟦ ƛ t ⟧ ρ a = ⊢⟦ t ⟧ ⟨ ρ , a ⟩
⊢⟦ r · s ⟧ ρ = ⊢⟦ r ⟧ ρ (⊢⟦ s ⟧ ρ)

-- Finally, the algorithm for normalization by evaluation
nbe : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → ∃[ t ] Nf T Γ t
nbe {Γ} t with ↓ᵀ (⊢⟦ t ⟧ (↑Γ Γ))
... | nf↑ t↑ = t↑ Γ

nf : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → Γ ⊢ T
nf t with nbe t
... | ⟨ t′ , _ ⟩ = t′

-- There are a few properties we want from this algorithm:
--   - Γ ⊢ nf(t) : T (well-typedness)
--   - ⟦ nf(t) ⟧ = ⟦ t ⟧ (preservation of meaning)
--   - nf(nf(t)) = nf(t) (idempotency)

-- As we are using an intrinsically typed representation of terms, the first
-- property is given to us automatically.

-- For preservation of meaning and idempotency, we have the following:

-- TODO: prove?
postulate
  preserve-meaning : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T} → ⊢⟦ nf t ⟧ ≡ ⊢⟦ t ⟧
  idempotent : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T} → nf (nf t) ≡ nf t

{- Section 2.6 -- Soundness -}

-- We want to prove the soundness of normalization,
-- i.e. Γ ⊢ t = nf(t) : T (there is a definitional
-- equality between t and nf(t) as determined by
-- βη-equivalence extended with rules characterizing
-- the computational behavior of primitive recursion,
-- as explained in section 2.2)
--
-- For this, a logical relation Ⓡ is defined such that
-- it implies Γ ⊢ t = nf(t) : T

-- First, we define a function for mapping a well-typed term in a
-- context Γ to a well-typed term in an extension of Γ, the context Γ′
-- TODO: look at exts/subst in DeBrujin section of PLFA
ext : ∀ {Γ Γ′ : Γ} {T : Type} → Γ′ Γ-≤ Γ → Γ ⊢ T → Γ′ ⊢ T
ext = {!!}

-- The Kripe logical relation

_Ⓡ_ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → ⟦ T ⟧ → Set

_Ⓡ_ {Γ₁} {nat} t 𝕟̂ with ↓ℕ̂ 𝕟̂
... | nf↑ v↑ =
  ∀ {Γ₂ : Γ}
  → (pf : Γ₂ Γ-≤ Γ₁)
  → (ext pf t) defeq (proj₁ (v↑ Γ₂))

_Ⓡ_ {Γ₁} {S ⇒ T} r f =
  ∀ {Γ₂ : Γ} {s : Γ₂ ⊢ S} {a : ⟦ S ⟧}
  → (pf : Γ₂ Γ-≤ Γ₁)
  → s Ⓡ a
  → ((ext pf r) · s) Ⓡ (f a)
