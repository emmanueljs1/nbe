import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open Eq using (_≡_; refl) renaming (sym to ≡-sym)

module Lemmas where

open import SystemT

-- Equivalent terms are definitionally equal
≡→== : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T}
     → t ≡ t′
       -------
     → t == t′
≡→== pf rewrite pf = refl

-- A few properties about the ≤ relation,
-- which are all required to prove irrelevance
-- of proof for the relation

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

-- Proof of context extension is irrelevant, and any
-- two proofs that a context is an extension of another
-- are equivalent
≤-pf-irrelevance : ∀ {Γ′ Γ : Γ}
       → (pf₁ : Γ′ ≤ Γ)
       → (pf₂ : Γ′ ≤ Γ)
       → pf₁ ≡ pf₂
≤-pf-irrelevance ≤-refl ≤-refl = refl
≤-pf-irrelevance ≤-refl (≤-, pf) = ⊥-elim (Γ≰Γ,T pf)
≤-pf-irrelevance (≤-, pf) ≤-refl = ⊥-elim (Γ≰Γ,T pf)
≤-pf-irrelevance (≤-, pf₁) (≤-, pf₂) rewrite ≤-pf-irrelevance pf₁ pf₂ = refl

-- Context extension is transitive
≤-trans : ∀ {Γ₃ Γ₂ Γ₁ : Γ}
        → Γ₃ ≤ Γ₂
        → Γ₂ ≤ Γ₁
          -------
        → Γ₃ ≤ Γ₁
≤-trans ≤-refl ≤-refl = ≤-refl
≤-trans ≤-refl (≤-, pf) = ≤-, pf
≤-trans (≤-, pf) ≤-refl = ≤-, pf
≤-trans (≤-, pf₁) (≤-, pf₂) = ≤-, (≤-trans pf₁ (≤-, pf₂))

-- Substitution / renaming lemmas

-- Renaming a lookup judgement is equivalent to applying the
-- renaming to a variable with that lookup judgement
rename≡[x]ᵨ : ∀ {Γ Δ : Γ} {T : Type} {x : Δ ∋ T} {σᵨ : Γ ⊩ᵨ Δ}
            → ` (rename x σᵨ) ≡ ` x [ σᵨ ]ᵨ
rename≡[x]ᵨ {x = `Z} {σᵨ , y} = refl
rename≡[x]ᵨ {x = `S x} {σᵨ , y} = rename≡[x]ᵨ {x = x} {σᵨ}

-- Applying a shifted renaming to a variable is equivalent
-- to incrementing the original renaming of the variable's
-- lookup judgemnet:
--   ` x [ σ ↑ ] ≡ `S (rename x σ) (where σ is a renaming substitution)
shift-var : ∀ {Γ Δ : Γ} {S T : Type} {x : Γ ∋ T} {σᵨ : Δ ⊩ᵨ Γ}
          → ` x [ substᵨ (_↑ᵨ {T = S} σᵨ) ] ≡ ` (`S (rename x σᵨ))
shift-var {x = `Z} {_ , _} = refl
shift-var {x = `S x} {σᵨ , _} = shift-var {x = x} {σᵨ}

-- Specialized version of the previous lemma
shift-rename : ∀ {Γ Δ : Γ} {S T : Type} {x : Γ ∋ T} {σᵨ : Δ ⊩ᵨ Γ}
            → rename x (_↑ᵨ {T = S} σᵨ) ≡ `S (rename x σᵨ)
shift-rename {x = `Z} {_ , _} = refl
shift-rename {x = `S x} {σᵨ , _} = shift-rename {x = x} {σᵨ}

-- Renaming with the identity renaming has no effect
rename-id : ∀ {Γ : Γ} {T : Type} {x : Γ ∋ T}
          → rename x idᵨ ≡ x
rename-id {x = `Z} = refl
rename-id {x = (`S_ {_} {S} x)}
  rewrite shift-rename {S = S} {x = x} {σᵨ = idᵨ} | rename-id {x = x} = refl

-- Shifting is commutative between renaming/substitution: a shifted
-- renaming substitution is equivalent to a substitution created from
-- a shifted renaming
shift-rename-subst : ∀ {Γ Δ : Γ} {T : Type} {σᵨ : Γ ⊩ᵨ Δ}
                   → substᵨ (_↑ᵨ {T = T} σᵨ) ≡ _↑ {T = T} (substᵨ σᵨ)
shift-rename-subst {σᵨ = ∅} = refl
shift-rename-subst {T = T} {σᵨ = _,_ {S = S} σᵨ x}
  rewrite shift-rename-subst {T = T} {σᵨ = σᵨ}
        | ≡-sym (rename≡[x]ᵨ {x = x} {σᵨ = _↑ᵨ {T = T} idᵨ})
        | shift-rename {S = T} {x = x} {σᵨ = idᵨ}
        | rename-id {x = x}                                 = refl

-- Lemma for expanding an identity substitution once
id≡↑id,x : ∀ {Γ : Γ} {T : Type} → id {Γ , T} ≡ (_↑ {T = T} id , ` `Z)
id≡↑id,x {∅} = refl
id≡↑id,x {Γ , T} {S}
  rewrite id≡↑id,x {Γ} {T}
        | shift-rename-subst {Γ , T} {Γ} {S} {σᵨ = idᵨ ↑ᵨ} = refl

-- The identity substititon has no effect
[id]-identity : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
              → t [ id ] ≡ t
[id]-identity {t = zero} = refl
[id]-identity {t = suc} = refl
[id]-identity {t = rec} = refl
[id]-identity {t = ` `Z} = refl
[id]-identity {t = ` (`S_ {_} {S} x)}
  rewrite shift-var {S = S} {x = x} {σᵨ = idᵨ} | rename-id {x = x} = refl
[id]-identity {Γ} {T} {ƛ_ {S} t}
  rewrite ≡-sym (id≡↑id,x {Γ} {S}) | [id]-identity {t = t} = refl
[id]-identity {t = r · s}
  rewrite [id]-identity {t = r} | [id]-identity {t = s} = refl

id-compose-identity : ∀ {Γ Δ : Γ} {σ : Γ ⊩ Δ}
                    → σ ∘ id ≡ σ
id-compose-identity {σ = ∅} = refl
id-compose-identity {σ = σ , s}
  rewrite id-compose-identity {σ = σ} | [id]-identity {t = s} = refl

postulate
  subst-compose : ∀ {Γ₁ Γ₂ Γ₃ : Γ} {T : Type} {τ : Γ₁ ⊩ Γ₂} {σ : Γ₂ ⊩ Γ₃}
                    {t : Γ₃ ⊢ T}
                → t [ σ ] [ τ ] ≡ t [ σ ∘ τ ]

  subst-compose-↑ : ∀ {Γ₁ Γ₂ Γ₃ : Γ} {S : Type} {τ : Γ₁ ⊩ Γ₂}
                      {σ : Γ₂ ⊩ Γ₃} {s : Γ₁ ⊢ S}
                  → (σ ↑) ∘ (τ , s) ≡ σ ∘ τ

  -- Weakening substitutions can be composed
  weaken-compose : ∀ {Γ₃ Γ₂ Γ₁ : Γ} {T : Type}
    → (Γ₃≤Γ₂ : Γ₃ ≤ Γ₂)
    → (Γ₂≤Γ₁ : Γ₂ ≤ Γ₁)
    → (t : Γ₁ ⊢ T)
    → Γ₃≤Γ₂ ≤⊢ Γ₂≤Γ₁ ≤⊢ t ≡ (≤-trans Γ₃≤Γ₂ Γ₂≤Γ₁) ≤⊢ t

  -- TODO: not sure if this lemma will be necessary
  ==-rename : ∀ {Γ Δ : Γ} {T : Type} {t t′ : Γ ⊢ T} {σᵨ : Δ ⊩ᵨ Γ}
            → t == t′
            → t [ σᵨ ]ᵨ == t′ [ σᵨ ]ᵨ

  ==-subst : ∀ {Γ Δ : Γ} {T : Type} {t t′ : Γ ⊢ T} {σ : Δ ⊩ Γ}
           → t == t′
           → t [ σ ] == t′ [ σ ]

-- Applying an increment renaming substitution to a term that already
-- has a weakening substitution applied to it is equivalent to shifting
-- the weakening substitution
incr-↑-≡ : ∀ {Γ Γ′ : Γ} {Γ′≤Γ : Γ′ ≤ Γ} {S T : Type} {t : Γ ⊢ T}
         → S ↑⊢ (t [ weaken Γ′≤Γ ]) ≡ t [ substᵨ (≤ᵨ Γ′≤Γ ↑ᵨ) ]
incr-↑-≡ {Γ′≤Γ = ≤-refl} {t = t} rewrite [id]-identity {t = t} = refl
incr-↑-≡ {Γ′≤Γ = ≤-, {T = S₁} Γ′≤Γ} {S₂} {t = t}
  rewrite ≡-sym (incr-↑-≡ {Γ′≤Γ = Γ′≤Γ} {S₁} {t = t})
        | weaken-compose (≤-, {T = S₁} ≤-refl) Γ′≤Γ t
        | weaken-compose
            (≤-, {T = S₂} ≤-refl)
            (≤-trans (≤-, {T = S₁} ≤-refl) Γ′≤Γ)
            t
        | ≤-pf-irrelevance
            (≤-trans (≤-, ≤-refl) (≤-trans (≤-, ≤-refl) Γ′≤Γ))
            (≤-, {T = S₂} (≤-, {T = S₁} Γ′≤Γ))                 = refl
