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

-- TODO: add de brujin indices to context?
data Γ : Set where
  ∅ : Γ
  _,_꞉_ : Γ → String → Ty → Γ

infix 11 _,_꞉_

data ⟨_꞉_⟩∈_ : String → Ty → Γ → Set where
  there : ∀ {x y : String} {S T : Ty} {Γ : Γ}
        → x ≢ y
        → ⟨ x ꞉ S ⟩∈ Γ
          --------------------
        → ⟨ x ꞉ S ⟩∈ Γ , y ꞉ T

  here : ∀ {x : String} {S : Ty} {Γ : Γ}
         --------------------
       → ⟨ x ꞉ S ⟩∈ Γ , x ꞉ S

infix 10 ⟨_꞉_⟩∈_

data Term : Set where
  zero  : Term
  suc   : Term → Term
  rec   : Term → Term → Term → Term
  var   : ∀ (x : String) → Term
  ƛ     : Term → Term
  _·_   : Term → Term → Term
  -- TODO : bound variable (de brujin index?)

data _⊢_꞉_ : Γ → Term → Ty → Set where
  ⊢-zero : ∀ {Γ : Γ}
         → Γ ⊢ zero ꞉ nat

  ⊢-suc : ∀ {Γ : Γ} {n : Term}
        → Γ ⊢ n ꞉ nat
        → Γ ⊢ suc n ꞉ nat

  ⊢-rec : ∀ {Γ : Γ} {T : Ty} {z s n : Term}
        → Γ ⊢ z ꞉ T
        → Γ ⊢ s ꞉ nat ⇒ T ⇒ T
        → Γ ⊢ n ꞉ nat
          -------------------
        → Γ ⊢ rec z s n ꞉ T

  -- the above rules are all separate as "constant" typing rules,
  -- it is unclear whether this difference is important. for
  -- suc, it results in an additional condition that the term
  -- being applied to suc is a nat

  ⊢-var : ∀ {T : Ty} {Γ : Γ} {x : String}
        → ⟨ x ꞉ T ⟩∈ Γ
        → Γ ⊢ var x ꞉ T

  ⊢-ƛ : ∀ {S T : Ty} {Γ : Γ} {t : Term}
      → Γ ⊢ t ꞉ T
        ---------------
      → Γ ⊢ ƛ t ꞉ S ⇒ T

  ⊢-· : ∀ {S T : Ty} {Γ : Γ} {r : Term} {s : Term}
      → Γ ⊢ r ꞉ S ⇒ T
      → Γ ⊢ s ꞉ S
        -------------
      → Γ ⊢ r · s ꞉ T

infixr 9 _⊢_꞉_

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
    Denotation.⟦ ⟦Γ⟧ ⟧ (Γ , _ ꞉ T) = ⟦ Γ ⟧ × ⟦ T ⟧
    -- TODO: instances for denotations of values
    -- TODO: denotation of a judgement
