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

-- We also define a relation detailing  when one context is the
-- extension of another, this is introduced formally in a later
-- section but will be useful throughout
data _≤_ : Γ → Γ → Set where
  -- A context extends itself
  ≤-refl : ∀ {Γ : Γ} → Γ ≤ Γ

  -- Given a context that extends another, the first
  -- can be extended further and the relation will
  -- still hold
  ≤-, : ∀ {Γ Γ′ : Γ} {T : Type}
      → Γ′ ≤ Γ
        ----------
      → Γ′ , T ≤ Γ

infix 4 _≤_

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
ex0 : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T ⇒ T
ex0 = ƛ ` (`Z)

-- (λx. x) zero
ex1 = ex0 · zero {∅}

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
-- for System T s.t. it implies equal interpretations
-- (thus making the proposition ⟦ nf(t) ⟧ = ⟦ t ⟧ decidable)

-- Before we define this extension, we define the functions
-- needed to establish βη-equivalence -- renaming and
-- substitution. Note that we've use the rules for parallel
-- substitution introduced in section 2.6, and design
-- all other relations and operations around them

-- A renaming between the contexts Γ and Δ
-- provides a variable in Γ to replace every
-- variable in Δ
data Renaming : Γ → Γ → Set where
  ∅ : ∀ {Γ : Γ} → Renaming Γ ∅

  _,_ : ∀ {Γ Δ : Γ} {S : Type}
      → Renaming Γ Δ
      → Γ ∋ S
        ------------------
      → Renaming Γ (Δ , S)

-- Shift the indices in a renaming by 1,
-- in other words for a renaming between Γ
-- and Δ, we can create a renaming between
-- Γ , T and Δ
--
-- We will use this to extend a renaming
-- under a binder
ρ-↑ : ∀ {Γ Δ : Γ} {T : Type}
    → Renaming Γ Δ
      ------------------
    → Renaming (Γ , T) Δ
ρ-↑ ∅ = ∅
ρ-↑ (ρ , x) with ρ-↑ ρ
... | ρ′ = ρ′ , (`S x)

-- The application of a renaming to rebase a term
-- from a context Δ to a context Γ, this is done
-- by using the renaming to replace all variables
-- used in the term by their corresponding variables
-- in Γ
rename : ∀ {Γ Δ : Γ} {T : Type}
        → Δ ⊢ T
        → Renaming Γ Δ
          ------------
        → Γ ⊢ T
rename zero ρ = zero
rename suc ρ = suc
rename rec ρ = rec
rename (` `Z) (ρ , x) = ` x
rename (` (`S x)) (ρ , _) = rename (` x) ρ
rename (ƛ t) ρ = ƛ rename t (ρ-↑ ρ , `Z)
rename (r · s) ρ = rename r ρ · rename s ρ

-- We also define a few renamings that
-- will be convenient for substitutions:

-- The identity renaming, defined
-- mutually with a renaming which
-- increments all indices in a context
ρ-id : ∀ {Γ : Γ} → Renaming Γ Γ
ρ-incr : ∀ {Γ : Γ} {T : Type} → Renaming (Γ , T) Γ

ρ-id {∅} = ∅
ρ-id {Γ , T} = ρ-incr , `Z

ρ-incr = ρ-↑ ρ-id

-- A renaming between a context Γ′ and Γ,
-- where Γ′ is an extension of Γ. This renaming
-- is really a series of shifts based on
-- how many extensions to Γ the context Γ′
-- contains
ρ-≤ : ∀ {Γ′ Γ : Γ} → Γ′ ≤ Γ → Renaming Γ′ Γ
ρ-≤ ≤-refl = ρ-id
ρ-≤ (≤-, pf) = ρ-↑ (ρ-≤ pf)

-- A parallel substitution Γ ⊢ σ : Δ provides
-- a well-typed term in Γ to substitute for
-- each variable in the context Δ
--
-- We use ⊩ instead of ⊢ since that is already reserved
-- for typing judgements (and keep using ∥ for the "parallel"
-- in "parallel substitutions" for operations related
-- to this type)
data _⊩_ : Γ → Γ → Set where
  ∅ : ∀ {Γ} → Γ ⊩ ∅

  _,_ : ∀ {Γ Δ : Γ} {S : Type}
        → Γ ⊩ Δ
        → Γ ⊢ S
          ---------
        → Γ ⊩ Δ , S

infix 4 _⊩_

-- Any renaming can be converted into a substitution
-- (for every variable in the context Δ we simply
-- use its corresponding variable in the context
-- Γ)
subst-ρ : ∀ {Γ Δ : Γ} → Renaming Γ Δ → Γ ⊩ Δ
subst-ρ ∅ = ∅
subst-ρ (ρ , x) = subst-ρ ρ , ` x

-- Shift the indices in a substitution by 1, as was
-- done for renamings
--
-- Similarly, we use this operation to extend a
-- substitution under a binder
_↑ : ∀ {Γ Δ : Γ} {T : Type}
      → Γ ⊩ Δ
        ---------
      → Γ , T ⊩ Δ
_↑ ∅ = ∅
_↑ (σ , s) = (σ ↑) , rename s ρ-incr

-- Application of a parallel substitution
-- Γ ⊢ σ : Δ to a term Δ ⊢ t : T (e.g. t[σ])
--
-- This operation is introduced in section 2.6
_∥[_]∥ : ∀ {Γ Δ : Γ} {T : Type}
     → Δ ⊢ T
     → Γ ⊩ Δ
       -----
     → Γ ⊢ T
zero ∥[ σ ]∥ = zero
suc ∥[ σ ]∥ = suc
rec ∥[ σ ]∥ = rec
(` `Z) ∥[ _ , x ]∥ = x
(` (`S x)) ∥[ σ , _ ]∥ = (` x) ∥[ σ ]∥
(ƛ t) ∥[ σ ]∥ = ƛ (t ∥[ σ ↑ , ` `Z ]∥)
(r · s) ∥[ σ ]∥ = (r ∥[ σ ]∥) · (s ∥[ σ ]∥)

-- We define a substitution that shifts
-- indices an arbitrary amount of times
-- to turn a context which extends
-- another context in the original context,
-- in other words a weakening substitution.
--
-- This substitution really is the renaming
-- between extended contexts
weaken : ∀ {Γ′ Γ : Γ}
       → Γ′ ≤ Γ
         ------
       → Γ′ ⊩ Γ
weaken pf = subst-ρ (ρ-≤ pf)

-- Additionally, we define an identity substitution,
-- which is simply the identity renaming
id : ∀ {Γ : Γ} → Γ ⊩ Γ
id = subst-ρ ρ-id

-- And now, we define an operation for
-- substituting the first free variable in a term
-- Γ , B ⊢ A with a term Γ ⊢ B,
-- to establish β equivalence. t [ s / x ] is
-- really shorthand for t [ id , s / x ]
_[_] : ∀ {Γ : Γ} {S T : Type}
  → Γ , T ⊢ S
  → Γ ⊢ T
    ---------
  → Γ ⊢ S
s [ t ] =  s ∥[ id , t ]∥

-- With these defined, we introduce a new relation between two
-- terms: definitional equality. In the thesis, this is
-- written as Γ ⊢ t = t′ : T, we will use t == t′ in Agda
-- (but continue using the first terminology in comments)
--
-- The relation is written such that the definitional equality
-- of two terms implies the equality of their interpretations
-- (Γ ⊢ t = t′ : T iff ⟦t⟧ = ⟦t′⟧); it is the extension of Βη
-- equivalence for System T suggested earlier
--
-- We will use this relation to prove the soundness of
-- NbE (i.e. ⟦nf(t)⟧ = ⟦t⟧)
data _==_ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → Γ ⊢ T → Set where

  -- Computation rules

  β-rec-z : ∀ {Γ : Γ} {T : Type}
              {z : Γ ⊢ T}
              {s : Γ ⊢ nat ⇒ T ⇒ T}
              -----------------------
            → rec · z · s · zero == z

  β-rec-s : ∀ {Γ : Γ} {T : Type}
      {z : Γ ⊢ T}
      {s : Γ ⊢ nat ⇒ T ⇒ T}
      {n : Γ ⊢ nat}
      ----------------------------------------------------
    → rec · z · s · (suc · n) == s · n · (rec · z · s · n)

  β-ƛ : ∀ {Γ : Γ} {S T : Type}
          {t : Γ , S ⊢ T}
          {s : Γ ⊢ S}
          --------------------
        → (ƛ t) · s == t [ s ]

  -- Function extensionality, i.e. Γ ⊢ t = Γ ⊢ λx. t x : S ⇒ T

  η : ∀ {Γ : Γ} {S T : Type}
        {t : Γ ⊢ S ⇒ T}
        ----------------------------
      → t == ƛ rename t ρ-incr · ` `Z

  -- Compatibility rules
  --
  -- Note that we do not need a rule for constants and variables as
  -- we are using an intrinsically typed representation, so refl
  -- catches all of these cases

  abs-compatible : ∀ {Γ : Γ} {S T : Type} {t t′ : Γ , S ⊢ T}
                   → t == t′
                     -----------
                   → ƛ t == ƛ t′

  app-compatible : ∀ {Γ : Γ} {S T : Type}
                     {r r′ : Γ ⊢ S ⇒ T} {s s′ : Γ ⊢ S}
                   → r == r′
                   → s == s′
                     ----------------
                   → r · s == r′ · s′

  -- Equivalence rules

  refl : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
           ------
         → t == t

  sym : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T}
        → t == t′
          -------
        → t′ == t

  trans : ∀ {Γ : Γ} {T : Type} {t₁ t₂ t₃ : Γ ⊢ T}
          → t₁ == t₂
          → t₂ == t₃
            --------
          → t₁ == t₃

infix 3 _==_

module ==-Reasoning where
  infix  1 begin_
  infixr 2 _==⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T}
    → t == t′
      ---------
    → t == t′
  begin pf = pf

  _==⟨_⟩_ : ∀ {Γ : Γ} {T : Type} {t₂ t₃ : Γ ⊢ T}
    → (t₁ : Γ ⊢ T)
    → t₁ == t₂
    → t₂ == t₃
      -----
    → t₁ == t₃
  t₁ ==⟨ t₁≡t₂ ⟩ t₂≡t₃  =  trans t₁≡t₂ t₂≡t₃

  _∎ : ∀ {Γ : Γ} {T : Type} → (t : Γ ⊢ T)
      -----
    → t == t
  t ∎  =  refl

open ==-Reasoning public

-- A few properties about the ≤ relation

invert-≤ : ∀ {Γ Γ′ : Γ} {T : Type}
         → Γ′ ≤ Γ , T
           ----------
         → Γ′ ≤ Γ
invert-≤ ≤-refl = ≤-, ≤-refl
invert-≤ (≤-, x) = ≤-, (invert-≤ x)

≤-,-uniq-T : ∀ {Γ Γ′ : Γ} {S T : Type}
           → Γ′ ≤ Γ , T
           → Γ′ ≤ Γ , S
             ----------
           → T ≡ S

≤-antisym : ∀ {Γ Γ′ : Γ}
          → Γ ≤ Γ′
          → Γ′ ≤ Γ
            ------
          → Γ ≡ Γ′

Γ≰Γ,T : ∀ {Γ : Γ} {T : Type} → ¬ (Γ ≤ Γ , T)

≤-,-uniq-T ≤-refl ≤-refl = refl
≤-,-uniq-T ≤-refl (≤-, c) = ⊥-elim (Γ≰Γ,T c)
≤-,-uniq-T (≤-, c) ≤-refl = ⊥-elim (Γ≰Γ,T c)
≤-,-uniq-T (≤-, p₁) (≤-, p₂)
  rewrite ≤-,-uniq-T p₁ p₂ = refl

≤-antisym ≤-refl Γ′≤Γ = refl
≤-antisym (≤-, Γ≤Γ′) ≤-refl = refl
≤-antisym (≤-, {T = T₁} p₁) (≤-, {T = T₂} p₂)
  with invert-≤ p₁ | invert-≤ p₂
... | ≤→         | ≤←
  with ≤-antisym ≤→ ≤←
... | refl
  rewrite ≤-,-uniq-T p₁ p₂ = refl

Γ≰Γ,T {Γ} {T} Γ≤Γ,T with ≤-, {T = T} (≤-refl {Γ})
... | Γ,T≤Γ
  with ≤-antisym Γ≤Γ,T Γ,T≤Γ
... | ()

≤-uniq : ∀ {Γ′ Γ : Γ}
       → (pf₁ : Γ′ ≤ Γ)
       → (pf₂ : Γ′ ≤ Γ)
       → pf₁ ≡ pf₂
≤-uniq ≤-refl ≤-refl = refl
≤-uniq ≤-refl (≤-, pf) = ⊥-elim (Γ≰Γ,T pf)
≤-uniq (≤-, pf) ≤-refl = ⊥-elim (Γ≰Γ,T pf)
≤-uniq (≤-, pf₁) (≤-, pf₂) rewrite ≤-uniq pf₁ pf₂ = refl

Γ≤∅ : ∀ {Γ : Γ} → Γ ≤ ∅
Γ≤∅ {∅} = ≤-refl
Γ≤∅ {Γ , _} with Γ≤∅ {Γ}
... | pf = ≤-, pf

_≤?_ : ∀ (Γ′ Γ : Γ) → Dec (Γ′ ≤ Γ)
∅ ≤? ∅ = yes ≤-refl
∅ ≤? (_ , _) = no λ()
(Γ , T) ≤? ∅ = yes Γ≤∅
(Γ′ , T) ≤? Γ@(_ , _)
  with (Γ′ , T) ≟Γ Γ
... | yes refl = yes ≤-refl
... | no Γ′≢Γ
  with Γ′ ≤? Γ
... | yes pf = yes (≤-, pf)
... | no ¬pf =
  no λ where
    ≤-refl → Γ′≢Γ refl
    (≤-, pf) → ¬pf pf

≤-trans : ∀ {Γ₃ Γ₂ Γ₁ : Γ}
        → Γ₃ ≤ Γ₂
        → Γ₂ ≤ Γ₁
          -------
        → Γ₃ ≤ Γ₁
≤-trans ≤-refl ≤-refl = ≤-refl
≤-trans ≤-refl (≤-, pf) = ≤-, pf
≤-trans (≤-, pf) ≤-refl = ≤-, pf
≤-trans (≤-, pf₁) (≤-, pf₂) = ≤-, (≤-trans pf₁ (≤-, pf₂))

-- Some lemmas around substitution/renaming
-- and its relation to definitional equality
-- that may or may not be useful

-- TODO: need a rename-subst-commute lemma

postulate
  -- TODO: prove ?
  ==-rename : ∀ {Γ Δ : Γ} {T : Type} {t t′ : Γ ⊢ T}
              {ρ : Renaming Δ Γ}
            → t == t′
            → rename t ρ == rename t′ ρ
