module SystemT where

open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

-- Basic system T

data Ty : Set where
  nat : Ty
  _⇒_ : ∀ (S T : Ty) → Ty

infixr 10 _⇒_

data Γ : Set where
  ∅ : Γ
  _,_ : Γ → (String × Ty) → Γ

data _∈_ : (String × Ty) → Γ → Set where
  append : ∀ (x : String) (S : Ty) (Γ : Γ)
           -------------------------------
         → ⟨ x , S ⟩ ∈ ( Γ , ⟨ x , S ⟩ )

data Cstᵀ : Ty → Set where
  zero : Cstᵀ nat

  suc  : Cstᵀ nat → Cstᵀ nat

  -- TODO: add metalanguage primitve recursion
  rec  : ∀ (T : Ty) → Cstᵀ (T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T)

data TmᵀΓ : Ty → Γ → Set where
  const : ∀ {T : Ty} {Γ : Γ}
        → Cstᵀ T
          --------
        → TmᵀΓ T Γ

  var : ∀ {S : Ty} {Γ : Γ}
      → (x : String)
        ------------------------
      → ⟨ x , S ⟩ ∈ Γ → TmᵀΓ S Γ

  ƛ : ∀ {S T : Ty} {Γ : Γ}
    → (x : String)
    → (t : TmᵀΓ T (Γ , ⟨ x , S ⟩))
      ----------------------------
    → TmᵀΓ (S ⇒ T) Γ

  _·_ : ∀ {S T : Ty} {Γ : Γ}
      → (r : TmᵀΓ (S ⇒ T) Γ)
      → (s : TmᵀΓ S Γ)
        --------------------
      → TmᵀΓ T Γ

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
    Denotation.⟦ ⟦Γ⟧ ⟧ (Γ , ⟨ _ , T ⟩) = ⟦ Γ ⟧ × ⟦ T ⟧
    -- TODO: instances for denotations of values
    -- TODO: denotation of a judgement
