module NbE where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SystemT

-- The normalization of terms in System T will involve dealing
-- with the interpretations of the types, terms, and contexts
-- of System T into our meta language
--
-- We use the following record to represent interpretations
-- of types, terms, and contexts in System T, indicated by ⟦_⟧.
-- This will help with the many definitions in the NbE
-- algorithm.
record Interpretation (D : Set) : Set₁ where
  field
    ⟦_⟧ : D → Set

open Interpretation {{...}} public

-- Most of the original interpretations of are left
-- out, as they will need to be updated to work with
-- the final NbE algorithm. They are, informally:
--
-- ⟦ nat ⟧ = ℕ
-- ⟦ S ⇒ T ⟧ = ⟦S⟧ → ⟦T⟧
--
-- ⟦ ∅ ⟧ = ⊤
-- ⟦ Γ , S ⟧ = ⟦ Γ ⟧ × ⟦ S ⟧
--
-- The metavariable ρ is used to represent elements of ⟦Γ⟧
-- For clarity we will not use an intrinsically typed de Brujin
-- representation in the following examples
--
-- The interpretation of a variable expects the interpretation
-- of a context, and is essentially a lookup
-- ⟦ Γ ∋ x:T ⟧ (ρ ∈ ⟦Γ⟧) ∈ ⟦ T ⟧
-- ⟦ Γ , T ∋ x:T ⟧ (ρ , a) = a
-- ⟦ Γ , y:S ∋ x:T ⟧ (ρ , _) = ⟦ Γ ∋ x:T ⟧ ρ
--
-- The interpretation of a typed term expects the interpretation
-- of a context as well. It is more involed, so we only include
-- the rule for variables and abstractions
-- ⟦ Γ ⊢ t : T ⟧ (ρ ∈ ⟦Γ⟧) = ⟦ T ⟧
-- ⟦ Γ ⊢ x : T ⟧ ρ = ⟦ Γ ∋ x:T ⟧ ρ
-- ⟦ Γ ⊢ λx . t : S ⇒ T ⟧ ρ  a  = ⟦ Γ , x:S ⊢ t : T ⟧ (ρ , a)

instance
    -- We only include the concrete interpretation of a
    -- context Γ, generalized over any interpretation of
    -- types, to be used with the actual interpretation
    -- defined later
    ⟦Γ⟧ : {{_ : Interpretation Type}} → Interpretation Γ
    Interpretation.⟦ ⟦Γ⟧ ⟧ ∅ = ⊤
    Interpretation.⟦ ⟦Γ⟧ ⟧ (Γ , T) = ⟦ Γ ⟧ × ⟦ T ⟧

{- Section 2.3 -- NbE sketch, neutral and normal terms -}

-- Normalization of terms in System T will be viewed as the evaulation of an
-- expression with unknowns (e.g. variables) to another, possibly simplified,
-- expression with unknowns. Normalized terms with unknowns will be referred to
-- as neutral terms, and normalized terms in general will be referred to as
-- normal terms.
--
-- The normal form of a typed term t in context Γ will be obtained by using
-- two functions: reflection and reification. Reflection takes a neutral
-- term into an interpration of that term, and reification takes an
-- interpretation of a term into a normal form. The following steps make
-- up a sketch of the algorithm:
--
--   1) reflect the variables of the context Γ
--      (all of which are neutral terms)
--   2) interpret the value of the term using the environment
--      of reflected variables
--   3) "reify" the interpreted value of the term (i.e. returning
--      it to a term in normal form
--
-- In this algorithm, the interpretation of a term will change subtly,
-- so that the interpretation of the base type nat is now normal
-- terms of a type nat. In other words, the interpretation of a
-- term of type nat may be one of 3 normal terms: zero, suc
-- applied to a normal term of type nat, and a neutral
-- term of type nat

-- We first give definitions for neutral and normal terms,
-- but do not yet give a formalization of the actual algorithm
-- itself

-- Neutral terms, indicated by metavariable 𝓊
data Ne (T : Type) (Γ : Γ) : Γ ⊢ T → Set
-- Normal terms, indicated by metavariable 𝓋
data Nf : (T : Type) → (Γ : Γ) → Γ ⊢ T → Set

-- Neutral terms are blocked terms in their normal form
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

-- Normal terms are terms in their normal form
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

{- Section 2.5 -- liftable terms, updated NbE algorithm -}

-- In the sketch of the NbE algorithm provided in section 2.3,
-- we use a context Γ of variables currently in scope to pick a "fresh"
-- variable (i.e. append a variable to the context, as we are using
-- De Brujin indices)
--
-- After this variable is reflected, it may later be reified in a different
-- context than it was created.
--
-- This is an issue with our intrinsically typed representation, as the
-- context Γ is part of the term itself, so it is incompatible with a
-- different context.
--
-- Even with an extrinsically typed representation it is something that has to
-- be handled explicitly at some point (i.e. to show that the resulting normal
-- form from the algorithm is well typed in its final context).
--
-- To address this, we use liftable terms. These are terms that are
-- generalized over contexts, and can be applied to any context Γ.
--
-- An effect of this is that it could be that the resulting term is not
-- well-typed. It will be the case that liftable neutral terms can only
-- be applied to extensions of the context under which they were created.
-- Because of this, liftable neutrals need return a placeholder value (tt)
-- for some contexts.
--
-- We write t↑ for the lifted version of a term t, and
-- 𝓋̂ and 𝓊̂ for the lifted version of the metavariables
-- 𝓋 and 𝓊

-- Liftable neutral term
Ne↑ : Type → Set
Ne↑ T = ∀ (Γ : Γ) → ∃[ t ] Ne T Γ t ⊎ ⊤

-- Liftable normal term
Nf↑ : Type → Set
Nf↑ T = ∀ (Γ : Γ) → ∃[ t ] Nf T Γ t

-- Application of liftable terms is overloaded,
-- i.e. (𝓊̂ 𝓋̂)(Γ) = 𝓊̂(Γ)𝓋̂(Γ)
--
-- We provide an operation for this for convenience
_·↑_ : ∀ {S T : Type} (𝓊̂ : Ne↑ (S ⇒ T)) (𝓋̂ : Nf↑ S)
    → ∀ (Γ : Γ) → ∃[ t ] Ne T Γ t ⊎ ⊤
_·↑_ 𝓊̂ 𝓋̂ Γ
  with 𝓊̂ Γ              | 𝓋̂ Γ
... | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩ | ⟨ 𝓋 , pf-𝓋 ⟩ =
      -- Note that we need to provide proof
      -- that our resulting lifted term is
      -- a neutral term as well
      inj₁ ⟨ 𝓊 · 𝓋 , ne-app pf-𝓊 pf-𝓋 ⟩
... | inj₂ tt           | _ = inj₂ tt

-- Since normalization by evaluation will need to be
-- over lifted terms, the concrete interpretation of
-- the base type nat will in the end be naturals
-- with embedded liftable neutrals
data ℕ̂ : Set where
  zero : ℕ̂
  suc : ℕ̂ → ℕ̂
  ne : Ne↑ nat → ℕ̂

instance
  ⟦Type⟧ : Interpretation Type
  Interpretation.⟦ ⟦Type⟧ ⟧ nat = ℕ̂
  Interpretation.⟦ ⟦Type⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧

-- With this, we begin the most important part
-- of normalization by evaluation, the reflection
-- and reification functions. These are mutually
-- recursive, and will be defined inductively
-- on the type T

-- Reflection of neutral terms of type T into
-- semantic objects in ⟦T⟧
↑ᵀ : {T : Type} → Ne↑ T → ⟦ T ⟧

-- Reification of semantic objects in ⟦T⟧ into
-- normal terms of type T
↓ᵀ : {T : Type} → ⟦ T ⟧ → Nf↑ T

-- ↑ᴺ - Reflection of neutral terms of type nat into ℕ̂,
--      here we just embed the liftable neutral
↑ᵀ {nat} 𝓊̂ = ne 𝓊̂

-- ↑ˢ⃗ᵗ - Reflection of neutral terms of type S ⇒ T,
--        into ⟦S⟧ → ⟦T⟧. We reify a semantic object in ⟦S⟧
--        and then reflect the neutral term resulting from the
--        application of the reified object to the original
--        neutral term

↑ᵀ {S ⇒ T} 𝓊̂ a = ↑ᵀ (𝓊̂ ·↑ (↓ᵀ a))

-- Given one context is an extension of another, and a
-- lookup judgement in the original context, there
-- is a corresponding lookup judgement in the extended context.
lookup-Γ-≤ : ∀ {Γ′ Γ : Γ} {T : Type}
           → Γ′ Γ-≤ Γ
           → Γ ∋ T
             --------
           → Γ′ ∋ T
lookup-Γ-≤ ≤-refl i = i
lookup-Γ-≤ (≤-, pf) i
  with lookup-Γ-≤ pf i
... | j = `S j

-- Create a new lifted variable of type S in the context Γ,
-- which can only be applied to extensions of Γ , S
𝓍̂ : ∀ {S : Type} (Γ₁ : Γ) → Ne↑ S
𝓍̂ {S} Γ₁ = var↑ where
  var↑ : ∀ (Γ₂ : Γ) → ∃[ t ] Ne S Γ₂ t ⊎ ⊤
  var↑ Γ₂ with Γ₂ Γ-≤? (Γ₁ , S)
  ... | yes pf  =
    inj₁ ⟨ ` x , ne-var x ⟩ where x = lookup-Γ-≤ pf `Z
  ... | no _    = inj₂ tt

-- ↓ᴺ - Reification of semantic objects of type ⟦N⟧, which
--      are our naturals with embedded liftable neutrals (ℕ̂).
--      For the interesting case of embedded liftable neutrals,
--      zero is used if the neutral cannot be lifted to the
--      context Γ
↓ℕ̂ : ⟦ nat ⟧ → Nf↑ nat
↓ℕ̂ zero = (λ _ → ⟨ zero , nf-zero ⟩)
↓ℕ̂ (suc n) with ↓ℕ̂ n
... | n↑ = suc↑ where
  suc↑ : (Γ : Γ) → ∃[ t ] Nf nat Γ t
  suc↑ Γ with n↑ Γ
  ... | ⟨ 𝓋 , pf ⟩ = ⟨ suc · 𝓋 , nf-suc pf ⟩
↓ℕ̂ (ne 𝓊̂) = 𝓋̂ where
  𝓋̂ : ∀ (Γ : Γ) → ∃[ t ] Nf nat Γ t
  𝓋̂ Γ with 𝓊̂ Γ
  ... | inj₁ ⟨ 𝓊 , pf ⟩ = ⟨ 𝓊 , nf-neutral pf ⟩
  ... | inj₂ tt         = ⟨ zero , nf-zero ⟩

↓ᵀ {nat} = ↓ℕ̂

-- ↓ˢ⃗ᵗ - Reification of semantic objects of type ⟦S → T⟧,
--        which are functions of type (⟦S⟧ → ⟦T⟧). The
--        resulting normal term is an abstraction over
--        the reification of the function applied to the
--        reflection of the bound variable
↓ᵀ {S ⇒ T} f = f↑ where
  f↑ : ∀ (Γ : Γ) → ∃[ t ] Nf (S ⇒ T) Γ t
  f↑ Γ with ↓ᵀ (f a) where a = ↑ᵀ (𝓍̂ Γ)
  ... | f·a↑
      with f·a↑ (Γ , S)
  ... | ⟨ 𝓋 , pf ⟩ = ⟨ ƛ 𝓋 , nf-abs pf ⟩

-- Reflection of a context gamma, this will be the reflected
-- environment over which a typed term in the context Γ
-- will be interpreted
↑Γ : ∀ (Γ : Γ) → ⟦ Γ ⟧
↑Γ ∅ = tt
↑Γ (Γ , T) = ⟨ ↑Γ Γ  , ↑ᵀ {T} (𝓍̂ Γ) ⟩

-- We also need to use reflection and reification to
-- define the interpretation of primitive recursion in
-- System T, which must work with liftable neutrals
--
-- Note: the original habilitation has the type of the first
-- argument to rec as "N" (nat), this seems to be a typo
⟦rec⟧ : ∀ {T : Type} → ⟦ T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T ⟧
⟦rec⟧ z s zero = z
⟦rec⟧ z s (suc n) = s n (⟦rec⟧ z s n)
⟦rec⟧ {T} z s (ne 𝓊̂) = ↑ᵀ rec↑ where
  rec↑ : ∀ (Γ : Γ) → ∃[ t ] Ne T Γ t ⊎ ⊤
  rec↑ Γ with 𝓊̂ Γ
  ... | inj₂ tt = inj₂ tt
  ... | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩
        with ↓ᵀ z  | ↓ᵀ s
  ... | z↑         | s↑
        with z↑ Γ      | s↑ Γ
  ... | ⟨ 𝓋z , pf-𝓋z ⟩ | ⟨ 𝓋s , pf-𝓋s ⟩ =
    inj₁ ⟨ rec · 𝓋z · 𝓋s · 𝓊 , ne-rec pf-𝓋z pf-𝓋s pf-𝓊 ⟩

-- Now that we have a concrete interpretation of types,
-- and an interpretation for primitive recursion,
-- we can define the corresponding interpretations of
-- the lookup and typing judgements
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
... | t↑ = t↑ Γ

nf : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → Γ ⊢ T
nf t with nbe t
... | ⟨ t′ , _ ⟩ = t′

-- Some examples of the algorithm in action:

-- normal form of (λx. x) zero is zero
nf-ex1 : nf ex1 ≡ zero
nf-ex1 with ex1
... | _ = refl

-- normal form of suc ((λx. x) zero) is suc zero
nf-ex2 : nf ex2 ≡ (suc · zero)
nf-ex2 with ex2
... | _ = refl

-- normal form of x:nat, y:nat ⊢ suc ((λz. suc y) x)
-- is x:nat, y:nat ⊢ suc (suc y)
nf-ex3 : nf ex3 ≡ (suc · (suc · ` (`Z)))
nf-ex3 with ex3
... | _ = refl

-- As for the properties we want from this algorithm:
--   - Γ ⊢ nf(t) : T (well-typedness)
--       We are using an intrinsically typed
--       representation of terms, so this property is
--       given to us automatically
--
--   - ⟦ nf(t) ⟧ = ⟦ t ⟧ (preservation of meaning)
--       We will prove this in the following section
--       using definitional equality [Soundness.agda]
--
--   - nf(nf(t)) = nf(t) (idempotency)
--       We have the following proposition:
postulate
  -- TODO: prove?
  idempotent : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
             → nf (nf t) ≡ nf t
