module SystemT where

open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≢_)

-- Basic system T

data Ty : Set where
  nat : Ty
  _⇒_ : ∀ (S T : Ty) → Ty

infixr 12 _⇒_

data Γ : Set where
  ∅ : Γ
  _,_ : Γ → Ty → Γ

infix 11 _,_

data _∋_ : Γ → Ty → Set where
  `Z_ : ∀ {Γ : Γ} {T : Ty}
        ---------
      → Γ , T ∋ T

  `S_ : ∀ {Γ : Γ} {S T : Ty}
      → Γ ∋ T
        ---------
      → Γ , S ∋ T

infix 10 _∋_

data _⊢_ (Γ : Γ) : Ty → Set where
  zero : Γ ⊢ nat

  suc : Γ ⊢ nat
        -------------
      → Γ ⊢ nat ⇒ nat

  -- TODO: add metalanguage primitve recursion
  rec  : ∀ {T : Ty}
       → Γ ⊢ T
       → Γ ⊢ nat ⇒ T ⇒ T
       → Γ ⊢ nat
         ---------------------------------
       → Γ ⊢ (T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T)

  `_ : ∀ {S : Ty}
     → Γ ∋ S
       -----
     → Γ ⊢ S

  ƛ : ∀ {S T : Ty}
    → Γ , S ⊢ T
      ---------
    → Γ ⊢ S ⇒ T

  _·_ : ∀ {S T : Ty}
      → Γ ⊢ S ⇒ T
      → Γ ⊢ S
        ---------
      → Γ ⊢ T

infix 9 _⊢_

-- TODO: add syntax declaration for typing judgement

record Denotation (D : Set) : Set₁ where
  field
    ⟦_⟧ : D → Set

open Denotation {{...}} public

⟦Ty⟧ : Denotation Ty
⟦Ty⟧ =
  record
    { ⟦_⟧ = denote }
  where
    denote : Ty → Set
    denote nat = ℕ
    denote (S ⇒ T) = (denote S) → (denote T)

instance
    ⟦Γ⟧ : ∀ {{_ : Denotation Ty}} → Denotation Γ
    Denotation.⟦ ⟦Γ⟧ ⟧ ∅ = ⊤
    Denotation.⟦ ⟦Γ⟧ ⟧ (Γ , T) = ⟦ Γ ⟧ × ⟦ T ⟧
    -- TODO: instances for denotations of values
    -- TODO: denotation of a judgement
