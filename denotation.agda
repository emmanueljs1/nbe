module Denotation where

open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

-- Basic system T

data Ty : Set where
  nat : Ty
  _arrow_ : ∀ (S T : Ty) → Ty

data Γ : Set where
  gamma : ∀ (l : List (String × Ty)) → Γ

data Set′ : Set where
  N : Set′
  N₁ : Set′
  S→T : ∀ (S₁ S₂ : Set′) → Set′
  _,_ : ∀ (S₁ S₂ : Set′) → Set′

{-
data Denoted : Set → Set → Set where
  ⟦_⟧ : ∀ (A : Set) → Denoted A ⊤
  ⟦_⟧_ : ∀ (A B : Set) → ⟦ A ⟧ → Denoted A B
-}

record ⟦_⟧ (A : Set) : Set where
  field
    denoted : ∀ (a : A) → Set′

record ⟦_⟧_ (A : Set) : Set where
  field
    denoted_val : ⟦ Γ ⟧ → ⟦ A ⟧

open ⟦_⟧

⟦Ty⟧ : ⟦ Ty ⟧
denoted ⟦Ty⟧ nat = N
denoted ⟦Ty⟧ (S arrow T) = S→T (denoted ⟦Ty⟧ S) (denoted ⟦Ty⟧ T)

⟦Γ⟧ : ⟦ Γ ⟧
denoted ⟦Γ⟧ (gamma []) = N₁
denoted ⟦Γ⟧ (gamma (⟨ _ , T ⟩ ∷ l)) = denoted ⟦Γ⟧ (gamma l) , denoted ⟦Ty⟧ T
