module SystemT where

open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (Dec; yes; no)

{- Section 2.1 -- Basic system T -}

-- Types in the language
data Type : Set where
  nat : Type
  _⇒_ : ∀ (S T : Type) → Type

infixr 12 _⇒_

-- Typing contexts
data Γ : Set where
  ∅ : Γ
  _,_ : Γ → Type → Γ

infix 11 _,_

-- Rules for determining when one context is the
-- extension of another
data Γ-extension : Γ → Γ → Set where
  ∅-extension : ∀ {Γ : Γ}
                ----------------
              → Γ-extension Γ ∅

  ,-extension : ∀ {Γ Γ′ : Γ} {T : Type}
              → Γ-extension Γ′ Γ
                ----------------------
              → Γ-extension (Γ′ , T) Γ

_Γ-extension?_ : ∀ (Γ′ Γ : Γ) → Dec (Γ-extension Γ′ Γ)
∅ Γ-extension? ∅ = yes ∅-extension
∅ Γ-extension? (_ , _) = no λ()
(_ , _) Γ-extension? ∅ = yes ∅-extension
(Γ′ , _) Γ-extension? Γ@(_ , _) with Γ′ Γ-extension? Γ
...  | yes pf  = yes (,-extension pf)
...  | no ¬pf  = no λ{ (,-extension pf) → ¬pf pf }

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

infix 10 _∋_

-- Given one context is an extension of another, and a
-- lookup judgement in the original context, there
-- is a corresponding lookup judgement in the extended context
lookup-extension : ∀ {Γ′ Γ : Γ} {T : Type}
                 → Γ-extension Γ′ Γ
                 → Γ ∋ T
                   ----------------
                 → Γ′ ∋ T
lookup-extension (,-extension pf) i
  with lookup-extension pf i
... | j = `S j

-- Typing judgement in a context
-- (these correspond to intrinsically typed terms)
data _⊢_ (Γ : Γ) : Type → Set where
  zero : Γ ⊢ nat

  suc : Γ ⊢ nat
        -------------
      → Γ ⊢ nat ⇒ nat

  -- TODO: add metalanguage primitve recursion
  --       for basic System T
  rec  : ∀ {T : Type}
       → Γ ⊢ T
       → Γ ⊢ nat ⇒ T ⇒ T
       → Γ ⊢ nat
         ---------------------------------
       → Γ ⊢ (T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T)

  `_ : ∀ {S : Type}
     → Γ ∋ S
       -----
     → Γ ⊢ S

  ƛ : ∀ {S T : Type}
    → Γ , S ⊢ T
      ---------
    → Γ ⊢ S ⇒ T

  _·_ : ∀ {S T : Type}
      → Γ ⊢ S ⇒ T
      → Γ ⊢ S
        ---------
      → Γ ⊢ T

infix 9 _⊢_

{- Section 2.1 --
     interpretations of types, terms, and contexts
     in System T
-}

record Denotation (D : Set) : Set₁ where
  field
    ⟦_⟧ : D → Set

open Denotation {{...}} public

⟦Type⟧ : Denotation Type
⟦Type⟧ =
  record
    { ⟦_⟧ = denote }
  where
    denote : Type → Set
    denote nat = ℕ
    denote (S ⇒ T) = (denote S) → (denote T)

instance
    ⟦Γ⟧ : ∀ {{_ : Denotation Type}} → Denotation Γ
    Denotation.⟦ ⟦Γ⟧ ⟧ ∅ = ⊤
    Denotation.⟦ ⟦Γ⟧ ⟧ (Γ , T) = ⟦ Γ ⟧ × ⟦ T ⟧
    -- TODO: instances for denotations of values
    -- TODO: denotation of a judgement
