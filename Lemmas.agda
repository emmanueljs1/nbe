import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open Eq using (_≡_; refl) renaming (sym to ≡-sym)

module Lemmas where

open import NbE

-- Equivalent terms are definitionally equal
≡→== : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
     → t ≡ t′
       -------
     → t == t′
≡→== pf rewrite pf = refl

-- A few properties about the ≤ relation,
-- which are all required to prove irrelevance
-- of proof for the relation

invert-≤ : ∀ {Γ Γ′ : Ctx} {T : Type}
         → Γ′ ≤ Γ , T
           ----------
         → Γ′ ≤ Γ
invert-≤ ≤-id = ≤-ext ≤-id
invert-≤ (≤-ext x) = ≤-ext (invert-≤ x)

≤-ext-uniq-T : ∀ {Γ Γ′ : Ctx} {S T : Type}
           → Γ′ ≤ Γ , T
           → Γ′ ≤ Γ , S
             ----------
           → T ≡ S

≤-antisym : ∀ {Γ Γ′ : Ctx}
          → Γ ≤ Γ′
          → Γ′ ≤ Γ
            ------
          → Γ ≡ Γ′

Γ≰Γ,T : ∀ {Γ : Ctx} {T : Type} → ¬ (Γ ≤ Γ , T)

≤-ext-uniq-T ≤-id ≤-id = refl
≤-ext-uniq-T ≤-id (≤-ext c) = ⊥-elim (Γ≰Γ,T c)
≤-ext-uniq-T (≤-ext c) ≤-id = ⊥-elim (Γ≰Γ,T c)
≤-ext-uniq-T (≤-ext p₁) (≤-ext p₂)
  rewrite ≤-ext-uniq-T p₁ p₂ = refl

≤-antisym ≤-id Γ′≤Γ = refl
≤-antisym (≤-ext Γ≤Γ′) ≤-id = refl
≤-antisym (≤-ext {T = T₁} p₁) (≤-ext {T = T₂} p₂)
  with invert-≤ p₁ | invert-≤ p₂
... | ≤→         | ≤←
  with ≤-antisym ≤→ ≤←
... | refl
  rewrite ≤-ext-uniq-T p₁ p₂ = refl

Γ≰Γ,T {Γ} {T} Γ≤Γ,T with ≤-ext {T = T} (≤-id {Γ})
... | Γ,T≤Γ
  with ≤-antisym Γ≤Γ,T Γ,T≤Γ
... | ()

-- Proof of context extension is irrelevant, and any
-- two proofs that a context is an extension of another
-- are equivalent
≤-pf-irrelevance : ∀ {Γ′ Γ : Ctx}
       → (pf₁ : Γ′ ≤ Γ)
       → (pf₂ : Γ′ ≤ Γ)
       → pf₁ ≡ pf₂
≤-pf-irrelevance ≤-id ≤-id = refl
≤-pf-irrelevance ≤-id (≤-ext pf) = ⊥-elim (Γ≰Γ,T pf)
≤-pf-irrelevance (≤-ext pf) ≤-id = ⊥-elim (Γ≰Γ,T pf)
≤-pf-irrelevance (≤-ext pf₁) (≤-ext pf₂) rewrite ≤-pf-irrelevance pf₁ pf₂ = refl

-- Context extension is transitive
≤-trans : ∀ {Γ₃ Γ₂ Γ₁ : Ctx}
        → Γ₃ ≤ Γ₂
        → Γ₂ ≤ Γ₁
          -------
        → Γ₃ ≤ Γ₁
≤-trans ≤-id ≤-id = ≤-id
≤-trans ≤-id (≤-ext pf) = ≤-ext pf
≤-trans (≤-ext pf) ≤-id = ≤-ext pf
≤-trans (≤-ext pf₁) (≤-ext pf₂) = ≤-ext (≤-trans pf₁ (≤-ext pf₂))

-- Substitution / renaming lemmas

-- Renaming a lookup judgement is equivalent to applying the
-- renaming to a variable with that lookup judgement
rename≡[x]ᵣ : ∀ {Γ Δ : Ctx} {T : Type} {x : Δ ∋ T} {σᵣ : Ren Γ Δ}
            → ` (rename x σᵣ) ≡ ` x [ σᵣ ]ᵣ
rename≡[x]ᵣ {x = `Z} {σᵣ , y} = refl
rename≡[x]ᵣ {x = `S x} {σᵣ , y} = rename≡[x]ᵣ {x = x} {σᵣ}

-- Applying a shifted renaming to a variable is equivalent
-- to incrementing the original renaming of the variable's
-- lookup judgemnet:
--   ` x [ σ ↑ ] ≡ `S (rename x σ) (where σ is a renaming substitution)
shift-var : ∀ {Γ Δ : Ctx} {S T : Type} {x : Γ ∋ T} {σᵣ : Ren Δ Γ}
          → ` x [ subst-ren (_↑ᵣ {T = S} σᵣ) ] ≡ ` (`S (rename x σᵣ))
shift-var {x = `Z} {_ , _} = refl
shift-var {x = `S x} {σᵣ , _} = shift-var {x = x} {σᵣ}

-- Specialized version of the previous lemma
shift-rename : ∀ {Γ Δ : Ctx} {S T : Type} {x : Γ ∋ T} {σᵣ : Ren Δ Γ}
            → rename x (_↑ᵣ {T = S} σᵣ) ≡ `S (rename x σᵣ)
shift-rename {x = `Z} {_ , _} = refl
shift-rename {x = `S x} {σᵣ , _} = shift-rename {x = x} {σᵣ}

-- Renaming with the identity renaming has no effect
rename-id : ∀ {Γ : Ctx} {T : Type} {x : Γ ∋ T}
          → rename x ren-id ≡ x
rename-id {x = `Z} = refl
rename-id {x = (`S_ {_} {S} x)}
  rewrite shift-rename {S = S} {x = x} {σᵣ = ren-id} | rename-id {x = x} = refl

-- Shifting is commutative between renaming/substitution: a shifted
-- renaming substitution is equivalent to a substitution created from
-- a shifted renaming
shift-rename-subst : ∀ {Γ Δ : Ctx} {T : Type} {σᵣ : Ren Γ Δ}
                   → subst-ren (_↑ᵣ {T = T} σᵣ) ≡ _↑ {T = T} (subst-ren σᵣ)
shift-rename-subst {σᵣ = ∅} = refl
shift-rename-subst {T = T} {σᵣ = _,_ {S = S} σᵣ x}
  rewrite shift-rename-subst {T = T} {σᵣ = σᵣ}
        | ≡-sym (rename≡[x]ᵣ {x = x} {σᵣ = _↑ᵣ {T = T} ren-id})
        | shift-rename {S = T} {x = x} {σᵣ = ren-id}
        | rename-id {x = x}                                 = refl

-- Lemma for expanding an identity substitution once
id≡↑id,x : ∀ {Γ : Ctx} {T : Type} → subst-id {Γ , T} ≡ (_↑ {T = T} subst-id , ` `Z)
id≡↑id,x {∅} = refl
id≡↑id,x {Γ , T} {S}
  rewrite id≡↑id,x {Γ} {T}
        | shift-rename-subst {Γ , T} {Γ} {S} {σᵣ = ren-id ↑ᵣ} = refl

-- The identity substititon has no effect
[id]-identity : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
              → t [ subst-id ] ≡ t
[id]-identity {t = zero} = refl
[id]-identity {t = suc} = refl
[id]-identity {t = rec} = refl
[id]-identity {t = ` `Z} = refl
[id]-identity {t = ` (`S_ {_} {S} x)}
  rewrite shift-var {S = S} {x = x} {σᵣ = ren-id} | rename-id {x = x} = refl
[id]-identity {Γ} {T} {ƛ_ {S} t}
  rewrite ≡-sym (id≡↑id,x {Γ} {S}) | [id]-identity {t = t} = refl
[id]-identity {t = r · s}
  rewrite [id]-identity {t = r} | [id]-identity {t = s} = refl

id-compose-identity : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ}
                    → σ ∘ subst-id ≡ σ
id-compose-identity {σ = ∅} = refl
id-compose-identity {σ = σ , s}
  rewrite id-compose-identity {σ = σ} | [id]-identity {t = s} = refl

postulate
  subst-compose : ∀ {Γ₁ Γ₂ Γ₃ : Ctx} {T : Type} {τ : Sub Γ₁ Γ₂} {σ : Sub Γ₂ Γ₃}
                    {t : Γ₃ ⊢ T}
                → t [ σ ] [ τ ] ≡ t [ σ ∘ τ ]

  subst-compose-↑ : ∀ {Γ₁ Γ₂ Γ₃ : Ctx} {S : Type} {τ : Sub Γ₁ Γ₂}
                      {σ : Sub Γ₂ Γ₃} {s : Γ₁ ⊢ S}
                  → (σ ↑) ∘ (τ , s) ≡ σ ∘ τ

  -- Weakening substitutions can be composed
  weaken-compose : ∀ {Γ₃ Γ₂ Γ₁ : Ctx} {T : Type}
    → (Γ₃≤Γ₂ : Γ₃ ≤ Γ₂)
    → (Γ₂≤Γ₁ : Γ₂ ≤ Γ₁)
    → (t : Γ₁ ⊢ T)
    → Γ₃≤Γ₂ ≤⊢ Γ₂≤Γ₁ ≤⊢ t ≡ (≤-trans Γ₃≤Γ₂ Γ₂≤Γ₁) ≤⊢ t

  -- TODO: not sure if this lemma will be necessary
  ==-rename : ∀ {Γ Δ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {σᵣ : Ren Δ Γ}
            → t == t′
            → t [ σᵣ ]ᵣ == t′ [ σᵣ ]ᵣ

  ==-subst : ∀ {Γ Δ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {σ : Sub Δ Γ}
           → t == t′
           → t [ σ ] == t′ [ σ ]

-- Applying an increment renaming substitution to a term that already
-- has a weakening substitution applied to it is equivalent to shifting
-- the weakening substitution
incr-↑-≡ : ∀ {Γ Γ′ : Ctx} {Γ′≤Γ : Γ′ ≤ Γ} {S T : Type} {t : Γ ⊢ T}
         → S ↑⊢ (t [ weaken Γ′≤Γ ]) ≡ t [ subst-ren (ren-≤ Γ′≤Γ ↑ᵣ) ]
incr-↑-≡ {Γ′≤Γ = ≤-id} {t = t} rewrite [id]-identity {t = t} = refl
incr-↑-≡ {Γ′≤Γ = ≤-ext {T = S₁} Γ′≤Γ} {S₂} {t = t}
  rewrite ≡-sym (incr-↑-≡ {Γ′≤Γ = Γ′≤Γ} {S₁} {t = t})
        | weaken-compose (≤-ext {T = S₁} ≤-id) Γ′≤Γ t
        | weaken-compose
            (≤-ext {T = S₂} ≤-id)
            (≤-trans (≤-ext {T = S₁} ≤-id) Γ′≤Γ)
            t
        | ≤-pf-irrelevance
            (≤-trans (≤-ext ≤-id) (≤-trans (≤-ext ≤-id) Γ′≤Γ))
            (≤-ext {T = S₂} (≤-ext {T = S₁} Γ′≤Γ))             = refl
