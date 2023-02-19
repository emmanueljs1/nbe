module SystemT where

open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
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

-- Some sample programs:

-- λx. x
id : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T ⇒ T
id = ƛ ` (`Z)

-- (λx. x) zero
ex1 = id · zero {∅}

-- suc ((λx. x) zero)
ex2 = suc · ex1

-- x:nat, y:nat ⊢ suc ((λz. suc y) x)
ex3 : ∅ , nat , nat ⊢ nat
ex3 = suc · ((ƛ suc · ` (`S `Z)) · ` (`S `Z))

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

Rename : Γ → Γ → Set
Rename Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A

-- Rename a well typed terms, enabling us to rebase from one
-- context to another (to establish η-equivalence)
rename : ∀ {Γ Δ}
  → Rename Γ Δ
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
_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
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
              {z : Γ ⊢ T}
              {s : Γ ⊢ nat ⇒ T ⇒ T}
              --------------------------
            → rec · z · s · zero def-≡ z

  ≡-β-rec-s : ∀ {Γ : Γ} {T : Type}
      {z : Γ ⊢ T}
      {s : Γ ⊢ nat ⇒ T ⇒ T}
      {n : Γ ⊢ nat}
      -------------------------------------------------------
    → rec · z · s · (suc · n) def-≡ s · n · (rec · z · s · n)

  ≡-β-ƛ : ∀ {Γ : Γ} {S T : Type}
          {t : Γ , S ⊢ T}
          {s : Γ ⊢ S}
          -----------------------
        → (ƛ t) · s def-≡ t [ s ]

  -- Function extensionality, i.e. Γ ⊢ t = Γ ⊢ λx. t x : S ⇒ T

  ≡-η : ∀ {Γ : Γ} {S T : Type}
        {t : Γ ⊢ S ⇒ T}
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

  ≡-refl : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
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

module def-≡-Reasoning where
  infix  1 begin_
  infixr 2 _def-≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T}
    → t def-≡ t′
      ---------
    → t def-≡ t′
  begin pf = pf

  _def-≡⟨_⟩_ : ∀ {Γ : Γ} {T : Type} {t₂ t₃ : Γ ⊢ T}
    → (t₁ : Γ ⊢ T)
    → t₁ def-≡ t₂
    → t₂ def-≡ t₃
      -----
    → t₁ def-≡ t₃
  t₁ def-≡⟨ t₁≡t₂ ⟩ t₂≡t₃  =  ≡-trans t₁≡t₂ t₂≡t₃

  _∎ : ∀ {Γ : Γ} {T : Type} → (t : Γ ⊢ T)
      -----
    → t def-≡ t
  t ∎  =  ≡-refl

open def-≡-Reasoning public

-- TODO: need a rename-subst-commute lemma

postulate
  -- TODO: prove ?
  def-≡-rename : ∀ {Γ Δ : Γ} {T : Type} {t t′ : Γ ⊢ T}
    {ρ : Rename Γ Δ}
    → t def-≡ t′ → rename ρ t def-≡ rename ρ t′
{-
def-≡-rename {t′ = t′} ≡-β-rec-z = ≡-trans ≡-β-rec-z ≡-refl
def-≡-rename ≡-β-rec-s = ≡-trans ≡-β-rec-s ≡-refl
def-≡-rename {t = (ƛ t) · s} {ρ = ρ} ≡-β-ƛ = ≡-trans ≡-β-ƛ {!!}
def-≡-rename ≡-η = {!!}
def-≡-rename (≡-abs-compatible defeq) = {!!}
def-≡-rename (≡-app-compatible defeq defeq₁) = {!!}
def-≡-rename ≡-refl = {!!}
def-≡-rename (≡-sym defeq) = {!!}
def-≡-rename (≡-trans defeq defeq₁) = {!!}
-}

-- We also define a relation detailing  when one context is the
-- extension of another, this is not introduced in this section,
-- but will be useful throughout (see [NbE.agda])
data _Γ-≤_ : Γ → Γ → Set where
  ≤-refl : ∀ {Γ : Γ} → Γ Γ-≤ Γ

  ≤-, : ∀ {Γ Γ′ : Γ} {T : Type}
      → Γ′ Γ-≤ Γ
        ------------
      → Γ′ , T Γ-≤ Γ

infix 4 _Γ-≤_

-- A few properties about the relation

Γ-≤-less : ∀ {Γ Γ′ : Γ} {T : Type}
         → Γ′ Γ-≤ Γ , T
         → Γ′ Γ-≤ Γ
Γ-≤-less ≤-refl = ≤-, ≤-refl
Γ-≤-less (≤-, x) = ≤-, (Γ-≤-less x)

Γ-≤-,-uniq-T : ∀ {Γ Γ′ : Γ} {S T : Type}
             → Γ′ Γ-≤ Γ , T
             → Γ′ Γ-≤ Γ , S
             → T ≡ S

Γ-≤-antisym : ∀ {Γ Γ′ : Γ}
            → Γ Γ-≤ Γ′
            → Γ′ Γ-≤ Γ
            → Γ ≡ Γ′

Γ≰Γ,T : ∀ {Γ : Γ} {T : Type} → ¬ (Γ Γ-≤ Γ , T)

Γ-≤-,-uniq-T ≤-refl ≤-refl = refl
Γ-≤-,-uniq-T ≤-refl (≤-, c) = ⊥-elim (Γ≰Γ,T c)
Γ-≤-,-uniq-T (≤-, c) ≤-refl = ⊥-elim (Γ≰Γ,T c)
Γ-≤-,-uniq-T (≤-, p₁) (≤-, p₂)
  rewrite Γ-≤-,-uniq-T p₁ p₂ = refl

Γ-≤-antisym ≤-refl Γ′≤Γ = refl
Γ-≤-antisym (≤-, Γ≤Γ′) ≤-refl = refl
Γ-≤-antisym (≤-, {T = T₁} p₁) (≤-, {T = T₂} p₂)
  with Γ-≤-less p₁ | Γ-≤-less p₂
... | ≤→ | ≤←
  with Γ-≤-antisym ≤→ ≤←
... | refl
  rewrite Γ-≤-,-uniq-T p₁ p₂ = refl

Γ≰Γ,T {Γ} {T} Γ≤Γ,T with ≤-, {T = T} (≤-refl {Γ})
... | Γ,T≤Γ
  with Γ-≤-antisym Γ≤Γ,T Γ,T≤Γ
... | ()

Γ-≤-uniq : ∀ {Γ′ Γ : Γ}
         → (pf₁ : Γ′ Γ-≤ Γ)
         → (pf₂ : Γ′ Γ-≤ Γ)
         → pf₁ ≡ pf₂
Γ-≤-uniq ≤-refl ≤-refl = refl
Γ-≤-uniq ≤-refl (≤-, pf) = ⊥-elim (Γ≰Γ,T pf)
Γ-≤-uniq (≤-, pf) ≤-refl = ⊥-elim (Γ≰Γ,T pf)
Γ-≤-uniq (≤-, pf₁) (≤-, pf₂) rewrite Γ-≤-uniq pf₁ pf₂ = refl

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

Γ-≤-trans : ∀ {Γ₃ Γ₂ Γ₁ : Γ}
        → Γ₂ Γ-≤ Γ₁
        → Γ₃ Γ-≤ Γ₂
          ---------
        → Γ₃ Γ-≤ Γ₁
Γ-≤-trans ≤-refl Γ₃≤Γ₂ = Γ₃≤Γ₂
Γ-≤-trans (≤-, Γ₂≤Γ₁) ≤-refl = ≤-, Γ₂≤Γ₁
Γ-≤-trans (≤-, Γ₂≤Γ₁) (≤-, Γ₃≤Γ₂) =
  ≤-, (Γ-≤-trans (≤-, Γ₂≤Γ₁) Γ₃≤Γ₂)
