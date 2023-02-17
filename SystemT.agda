module SystemT where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- Section 2.1 -- System T -}

-- We start off by defining the language that we will
-- use to showcase normalization by evaluation, System T.
--
-- It has natural numbers, higher-order functions, and
-- primitive recursion. We will define it with intrinsic
-- typing, and use a de Brujin index representation
-- for variables

-- Types in the language
data Type : Set where
  nat : Type
  _⇒_ : ∀ (S T : Type) → Type

infixr 7 _⇒_

_≟Tp_ : ∀ (S T : Type) → Dec (S ≡ T)
nat ≟Tp nat = yes refl
nat ≟Tp (S ⇒ T) = no λ()
(S₁ ⇒ T₁) ≟Tp nat = no λ()
(S₁ ⇒ T₁) ≟Tp (S₂ ⇒ T₂) with S₁ ≟Tp S₂ | T₁ ≟Tp T₂
... | no ¬pf   | no _      = no (λ where refl → ¬pf refl)
... | no ¬pf   | yes _     = no (λ where refl → ¬pf refl )
... | yes _    | no ¬pf    = no (λ where refl → ¬pf refl)
... | yes refl | yes refl  = yes refl

-- Typing contexts
data Γ : Set where
  ∅ : Γ
  _,_ : Γ → Type → Γ

infixl 5 _,_

_≟Γ_ : ∀ (Γ′ Γ : Γ) → Dec (Γ′ ≡ Γ)
∅ ≟Γ ∅ = yes refl
∅ ≟Γ (_ , _) = no λ()
(_ , _) ≟Γ ∅ = no λ()
(Γ′ , S) ≟Γ (Γ , T) with Γ′ ≟Γ Γ | S ≟Tp T
... | no ¬pf   | no _     = no (λ where refl → ¬pf refl)
... | no ¬pf   | yes _    = no (λ where refl → ¬pf refl)
... | yes _    | no ¬pf   = no (λ where refl → ¬pf refl)
... | yes refl | yes refl = yes refl

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

-- Rules for determining when one context is the
-- extension of another, this is not introduced in this section,
-- but will be useful throughout
data _Γ-≤_ : Γ → Γ → Set where
  ≤-refl : ∀ {Γ : Γ} → Γ Γ-≤ Γ

  ≤-, : ∀ {Γ Γ′ : Γ} {T : Type}
      → Γ′ Γ-≤ Γ
        ------------
      → Γ′ , T Γ-≤ Γ

infix 4 _Γ-≤_

Γ≤∅ : ∀ {Γ : Γ} → Γ Γ-≤ ∅
Γ≤∅ {∅} = ≤-refl
Γ≤∅ {Γ , _} with Γ≤∅ {Γ}
... | pf = ≤-, pf

_Γ-≤?_ : ∀ (Γ′ Γ : Γ) → Dec (Γ′ Γ-≤ Γ)
∅ Γ-≤? ∅ = yes ≤-refl
∅ Γ-≤? (_ , _) = no λ()
(Γ , T) Γ-≤? ∅ = yes Γ≤∅
(Γ′ , T) Γ-≤? Γ@(_ , _)
  with (Γ′ , T) ≟Γ Γ
... | yes refl = yes ≤-refl
... | no Γ′≢Γ
  with Γ′ Γ-≤? Γ
... | yes pf = yes (≤-, pf)
... | no ¬pf =
  no λ where
    ≤-refl → Γ′≢Γ refl
    (≤-, pf) → ¬pf pf

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

-- Most of the original interpretations of of this section are left
-- out, as the version needs to be updated to work with the final
-- NbE algorithm. They are, informally:
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

{- Section 2.2 -- soundness of normalization -}

-- We expect the following soundness properties for a
-- normalization algorithm nf(t) that produces a normal form
-- for a typed term Γ ⊢ t : T
--
--   - Γ ⊢ nf(t) : T (well-typedness of normal form)
--   - ⟦ nf(t) ⟧ = ⟦ t ⟧ (preservation of meaning)
--   - nf(nf(t)) = nf(t) (idempotency)
--
-- For preservation of meaning, our interpretations of
-- functional terms are functions, whose equality is
-- undecidable. However, in STLC, we have that two terms
-- are βη-equivalent iff their interpretationss are equal.
-- So, we wish to define an extension of βη-equivalence
-- for System T s.t. it implies equal interpretationss
-- (thus making the proposition ⟦ nf(t) ⟧ = ⟦ t ⟧ decidable)

-- Before we define this extension, we define the functions
-- needed to establish βη-equivalence -- renaming and
-- substitution

ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ `Z      =  `Z
ext ρ (`S x)  =  `S (ρ x)

-- Rename a well typed terms, enabling us to rebase from one
-- context to another (to establish η-equivalence)
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ zero = zero
rename ρ suc = suc
rename ρ rec = rec
rename ρ (` x) = ` ρ x
rename ρ (ƛ t) = ƛ rename (ext ρ) t
rename ρ (r · s) = rename ρ r · rename ρ s

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ `Z      =  ` `Z
exts σ (`S x)  =  rename `S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x)          =  σ x
subst σ (ƛ t)          =  ƛ (subst (exts σ) t)
subst σ (r · s)        =  (subst σ r) · (subst σ s)
subst σ zero           =  zero
subst σ suc            =  suc
subst σ rec            =  rec

-- Substitute the first free variable in a term
-- Γ , B ⊢ A with a term Γ ⊢ B (to establish β equivalence)
_[_/`Z] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_/`Z] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ `Z      =  M
  σ (`S x)  =  ` x

-- With these defined, we introduce a new relation between two
-- terms: definitional equality. The relation is written such
-- that the definitional equality of two terms implies the
-- equality of their interpretations (t def-≡ t′ iff ⟦t⟧ = ⟦t′⟧),
-- it is the extension of Βη equivalence for System T
-- suggested earlier
--
-- We will use this to prove the soundness of
-- NbE (i.e. ⟦nf(t)⟧ = ⟦t⟧)

data _def-≡_ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → Γ ⊢ T → Set where

  -- Computation rules

  ≡-β-rec-z : ∀ {Γ : Γ} {T : Type}
            → (z : Γ ⊢ T)
            → (s : Γ ⊢ nat ⇒ T ⇒ T)
              --------------------------
            → rec · z · s · zero def-≡ z

  ≡-β-rec-s : ∀ {Γ : Γ} {T : Type}
    → (z : Γ ⊢ T)
    → (s : Γ ⊢ nat ⇒ T ⇒ T)
    → (n : Γ ⊢ nat)
      -------------------------------------------------------
    → rec · z · s · (suc · n) def-≡ s · n · (rec · z · s · n)

  ≡-β-ƛ : ∀ {Γ : Γ} {S T : Type}
        → (t : Γ , S ⊢ T)
        → (s : Γ ⊢ S)
          --------------------------
        → (ƛ t) · s def-≡ t [ s /`Z]

  -- Function extensionality, i.e. Γ ⊢ t = Γ ⊢ λx. t x : S ⇒ T

  ≡-η : ∀ {Γ : Γ} {S T : Type}
      → (t : Γ ⊢ S ⇒ T)
        -------------------------------
      → t def-≡ ƛ (rename `S_ t) · ` `Z

  -- Compatibility rules
  --
  -- Note that we do not need a rule for constants and variables as
  -- we are using an intrinsically typed representation, so ≡-refl
  -- catches all of these cases

  ≡-abs-compatible : ∀ {Γ : Γ} {S T : Type} {t t′ : Γ , S ⊢ T}
                   → t def-≡ t′
                     -------------
                   → ƛ t def-≡ ƛ t′

  ≡-app-compatible : ∀ {Γ : Γ} {S T : Type}
                       {r r′ : Γ ⊢ S ⇒ T} {s s′ : Γ ⊢ S}
                   → r def-≡ r′
                   → s def-≡ s′
                     ------------------
                   → r · s def-≡ r′ · s′

  -- Equivalence rules

  ≡-refl : ∀ {Γ : Γ} {T : Type}
         → (t : Γ ⊢ T)
           -----------
         → t def-≡ t

  ≡-sym : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T}
        → t def-≡ t′
          ----------
        → t′ def-≡ t

  ≡-trans : ∀ {Γ : Γ} {T : Type} {t₁ t₂ t₃ : Γ ⊢ T}
          → t₁ def-≡ t₂
          → t₂ def-≡ t₃
            -----------
          → t₁ def-≡ t₃


infix 3 _def-≡_

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

data Ne (T : Type) (Γ : Γ) : Γ ⊢ T → Set     -- Neutral terms
data Nf : (T : Type) → (Γ : Γ) → Γ ⊢ T → Set -- Normal terms

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
-- We write t↑ for the lifted version of a term t

-- Liftable neutral term
data Ne↑ (T : Type) : Set where
  ne↑ : (∀ (Γ : Γ) → ((∃[ t ] Ne T Γ t) ⊎ ⊤)) → Ne↑ T

-- Liftable normal term
data Nf↑ (T : Type) : Set where
  nf↑ : (∀ (Γ : Γ) → ∃[ t ] Nf T Γ t) → Nf↑ T

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
↑ᵀ {S ⇒ T} (ne↑ 𝓊↑) a with ↓ᵀ a
...  | nf↑ v↑ = ↑ᵀ (ne↑ 𝓊·v↑) where
  𝓊·v↑ : ∀ (Γ : Γ) → (∃[ t ] Ne T Γ t) ⊎ ⊤
  𝓊·v↑ Γ with 𝓊↑ Γ        | v↑ Γ
  ... | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩ | ⟨ 𝓋 , pf-𝓋 ⟩ = inj₁ ⟨ 𝓊 · 𝓋 , ne-app pf-𝓊 pf-𝓋 ⟩
  ... | inj₂ tt           | _ = inj₂ tt

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

-- Reflection of a context gamma, this will be the reflected
-- environment over which a typed term in the context Γ
-- will be interpreted
↑Γ : ∀ (Γ : Γ) → ⟦ Γ ⟧
↑Γ ∅ = tt
↑Γ (Γ , T) = ⟨ ↑Γ Γ  , ↑ᵀ {T} (mk-lifted-var Γ) ⟩

-- We also need to use reflection and reification to
-- define the interpretation of primitive recursion in
-- System T, which must work with liftable neutrals
--
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
... | nf↑ t↑ = t↑ Γ

nf : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → Γ ⊢ T
nf t with nbe t
... | ⟨ t′ , _ ⟩ = t′

-- As for the properties we want from this algorithm:
--   - Γ ⊢ nf(t) : T (well-typedness)
--       We are using an intrinsically typed
--       representation of terms, so this property is
--       given to us automatically
--
--   - ⟦ nf(t) ⟧ = ⟦ t ⟧ (preservation of meaning)
--       We will prove this in the following section
--       using definitional equality
--
--   - nf(nf(t)) = nf(t) (idempotency)
--       We have the following proposition:
postulate
  -- TODO: prove?
  idempotent : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
             → nf (nf t) ≡ nf t

{- Section 2.6 -- Soundness -}

-- We prove the soundness of normalization by proving
-- the definitional equality of a term and its normal form
-- i.e. Γ ⊢ t = nf(t) : T
--
-- For this, a logical relation Ⓡ is defined such that
-- it implies Γ ⊢ t = nf(t) : T

-- We start by defining a few functions for
-- the convenience of defining the relation

-- The first extends a well typed term in context Γ to its corresponding
-- well typed term in Γ′, an extension of Γ
_ext-⊢_ : ∀ {Γ′ Γ : Γ} {T : Type} → Γ′ Γ-≤ Γ → Γ ⊢ T → Γ′ ⊢ T
pf ext-⊢ t = rename (lookup-Γ-≤ pf) t

infix 4 _ext-⊢_

-- The next function we define "lifts"
-- definitional equality over liftable neutrals
_def-≡↑_ : {Γ : Γ} {T : Type} → Γ ⊢ T → Ne↑ T → Set
_def-≡↑_ {Γ} t (ne↑ 𝓊↑) with 𝓊↑ Γ
... | inj₁ ⟨ 𝓊 , _ ⟩ = t def-≡ 𝓊
... | inj₂ _ = ⊥

infix 3 _def-≡↑_

-- The Kripe logical relation between a typed term Γ ⊢ T and a
-- value in ⟦T⟧

_Ⓡ_ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → ⟦ T ⟧ → Set

_Ⓡ_ {_} {nat} t zero = t def-≡ zero
_Ⓡ_ {Γ} {nat} t (suc 𝓋̂) = ∃[ n ] n Ⓡ 𝓋̂ × t def-≡ (suc · n)
_Ⓡ_ {Γ₁} {nat} t (ne 𝓊̂) =
  ∀ {Γ₂ : Γ}
  → (Γ′ : Γ₂ Γ-≤ Γ₁)
    ----------------
  → Γ′ ext-⊢ t def-≡↑ 𝓊̂

_Ⓡ_ {Γ₁} {S ⇒ T} r f =
  ∀ {Γ₂ : Γ} {s : Γ₂ ⊢ S} {a : ⟦ S ⟧}
  → (Γ′ : Γ₂ Γ-≤ Γ₁)
  → s Ⓡ a
    --------------------
  → (Γ′ ext-⊢ r) · s Ⓡ f a

infix 4 _Ⓡ_

defeq→Ⓡ : ∀ {Γ Γ′ : Γ} {T : Type} {𝓊 : Γ′ ⊢ T} {𝓊̂ : Ne↑ T}
        → (Γ′ Γ-≤ Γ → 𝓊 def-≡↑ 𝓊̂)
          -----------------------
        → 𝓊 Ⓡ (↑ᵀ 𝓊̂)
defeq→Ⓡ = {!!}
