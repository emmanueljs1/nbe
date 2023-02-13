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

data Cstᵀ : Ty → Set where
  zero : Cstᵀ nat

  suc : Cstᵀ (nat ⇒ nat)

  -- TODO: add metalanguage primitve recursion
  rec  : ∀ (T : Ty) → Cstᵀ (T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T)

data _⊢_ : Γ → Ty → Set where
  const : ∀ {T : Ty} {Γ : Γ}
        → Cstᵀ T
          --------
        → Γ ⊢ T

  -- todo: add debrujin term?
  var : ∀ {S : Ty} {Γ : Γ} {x : String}
      → ⟨ x ꞉ S ⟩∈ Γ
        ------------
      → Γ , x ꞉ S ⊢ S

  -- TODO: use debrujin indices
  ƛ : ∀ {S T : Ty} {Γ : Γ}
    → (x : String)
    → Γ , x ꞉ S ⊢ T
      -------------
    → Γ ⊢ S ⇒ T

  _·_ : ∀ {S T : Ty} {Γ : Γ}
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
    Denotation.⟦ ⟦Γ⟧ ⟧ (Γ , x ꞉ T) = ⟦ Γ ⟧ × ⟦ T ⟧
    -- TODO: instances for denotations of values
    -- TODO: denotation of a judgement
