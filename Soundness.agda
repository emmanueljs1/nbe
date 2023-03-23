module Soundness where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (yes; no)
open Eq using (refl; _≡_) renaming (sym to ≡-sym; trans to ≡-trans)

open import SystemT
open import NbE

{- Section 2.6 -- Soundness -}

-- We prove the soundness of normalization by proving
-- the definitional equality of a term and its normal form
-- i.e. Γ ⊢ t = nf(t) : T, which expands to:
--
--   Γ ⊢ t = ↓ᵀ a Γ where a = ⟦ t ⟧
--
-- For this, a logical relation t Ⓡ a is defined such that
-- it implies Γ ⊢ t = ↓ᵀ a Γ : T

-- We start by defining a few functions for the convenience of
-- defining the relation

-- The first extends a well typed term in context Γ to its
-- corresponding well typed term in Γ′, an extension of Γ.
--
-- Formally, this represents the changing of contexts
-- used in the Kripe logical relation, e.g.
-- Γ ⊢ t : T --> Γ′ ⊢ t : T
--
-- Really, this is just notation for applying a weakening
-- substitution
_≤⊢_ : ∀ {Γ′ Γ : Γ} {T : Type} → Γ′ ≤ Γ → Γ ⊢ T → Γ′ ⊢ T
pf ≤⊢ t = t [ weaken pf ]

infixr 5 _≤⊢_

-- The next function we define "lifts"
-- definitional equality over liftable neutrals
--
-- Formally, this represents the condition seen
-- in the Kripke logical relation:
--   Γ ⊢ 𝓊 = 𝓊̂(Γ) : T
-- or, equivalently in our syntax:
_==↑_ : {Γ : Γ} {T : Type} → Γ ⊢ T → Ne↑ T → Set
_==↑_ {Γ} t 𝓊̂ with 𝓊̂ Γ
... | inj₁ ⟨ 𝓊 , _ ⟩ =
      -- If the liftable neutral can be lifted to the
      -- context Γ, this is just definitional equality
      t == 𝓊
... | inj₂ _ =
      -- Otherwise, the proposition cannot be proven,
      -- as there is no lifted term in the context
      -- to compare a term to
      ⊥

infix 3 _==↑_

-- We also define a function for definitional equality
-- over naturals with embedded liftable neutrals. This
-- represents the condition:
--   Γ ⊢ t = 𝓋̂(Γ) : nat
-- that is used in the logical relation between typed terms
-- and semantic objects at type nat.
_==ℕ̂_ : {Γ : Γ} → Γ ⊢ nat → ⟦ nat ⟧ → Set
_==ℕ̂_ t zero = t == zero
_==ℕ̂_ {Γ} t (suc 𝓋̂) =
  ∃[ n ] t == suc · n ×
    (∀ {Γ′ : SystemT.Γ} → (Γ′≤Γ : Γ′ ≤ Γ) → Γ′≤Γ ≤⊢ n ==ℕ̂ 𝓋̂)
_==ℕ̂_ t (ne 𝓊̂) = t ==↑ 𝓊̂

infix 3 _==ℕ̂_

-- The next function provides a shorthand for reifying
-- an interpretation of T then immediately applying a
-- context Γ, as is done in some implications (we use lowercase
-- γ as our subscript as Γ is not an option).
↓ᵀᵧ : ∀ {Γ : Γ} {T : Type} → (a : ⟦ T ⟧) → Γ ⊢ T
↓ᵀᵧ {Γ} a with ↓ᵀ a
... | a↑ = proj₁ (a↑ Γ)

-- We now introduce the Kripe logical relation between a typed term
-- Γ ⊢ t : T and a value in ⟦T⟧, it is constructed by induction on
-- types
_Ⓡ_ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → ⟦ T ⟧ → Set

-- The relation defined over nats:
-- Γ : nat Ⓡ 𝓋̂ =
--     ∀ Γ′ ≤ Γ. Γ′ ⊢ t = 𝓋̂(Γ′) : nat
_Ⓡ_ {Γ} {nat} t 𝓋̂ =
  ∀ {Γ′ : SystemT.Γ}
  → (Γ′≤Γ : Γ′ ≤ Γ)
    ---------------
  → Γ′≤Γ ≤⊢ t ==ℕ̂ 𝓋̂

-- The relation defined over functions:
--   Γ ⊢ r : S → T Ⓡ f =
--     ∀ Γ′ ≤ Γ. Γ′ ⊢ s : S Ⓡ a ⇒ Γ′ ⊢ r s : T Ⓡ f(a)
_Ⓡ_ {Γ} {S ⇒ T} r f =
  ∀ {Γ′ : SystemT.Γ}
  → (Γ′≤Γ : Γ′ ≤ Γ)
  → ∀ {s : Γ′ ⊢ S} {a : ⟦ S ⟧}
  → s Ⓡ a
    ----------------------
  → (Γ′≤Γ ≤⊢ r) · s Ⓡ f a

infix 4 _Ⓡ_

-- Some lemmas about Kripe logical relations

-- Kripe logical relations are transitive with respect to
-- definitional equality
==-Ⓡ : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T} {a : ⟦ T ⟧}
     → t == t′
     → t Ⓡ a
       -------
     → t′ Ⓡ a
==-Ⓡ {T = nat} {a = zero} t==t′ pf Γ′≤Γ =
  trans (sym (==-subst t==t′)) (pf Γ′≤Γ)
==-Ⓡ {T = nat} {a = suc a} t==t′ pf Γ′≤Γ
  with pf Γ′≤Γ
... | ⟨ n , ⟨ t==sn , n==a ⟩ ⟩ =
  ⟨ n , ⟨ trans (sym (==-subst t==t′)) t==sn , n==a ⟩ ⟩
==-Ⓡ {T = nat} {a = ne 𝓊̂} t==t′ pf {Γ′} Γ′≤Γ
  with 𝓊̂ Γ′          | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩ | t==𝓊 =
  trans (sym (==-subst t==t′)) t==𝓊
==-Ⓡ {T = S ⇒ T} t==t′ pf Γ′≤Γ sⓇa =
  ==-Ⓡ (app-compatible (==-subst t==t′) refl) (pf Γ′≤Γ sⓇa)

-- If the logical relation Γ ⊢ t : T Ⓡ a holds, then for all Γ′ ≤ Γ,
-- Γ′ ⊢ t : T Ⓡ a holds as well
Ⓡ-ext : ∀ {Γ′ Γ : Γ} {T : Type} {Γ′≤Γ : Γ′ ≤ Γ} {t : Γ ⊢ T} {a : ⟦ T ⟧}
      → t Ⓡ a
      → Γ′≤Γ ≤⊢ t Ⓡ a
Ⓡ-ext {T = nat} {Γ′≤Γ} {t} pf Γ″≤Γ′
  rewrite weaken-compose Γ″≤Γ′ Γ′≤Γ t = pf (≤-trans Γ″≤Γ′ Γ′≤Γ)
Ⓡ-ext {T = S ⇒ T} {Γ′≤Γ} {t} pf Γ″≤Γ′ sⓇa
  rewrite weaken-compose Γ″≤Γ′ Γ′≤Γ t = pf (≤-trans Γ″≤Γ′ Γ′≤Γ) sⓇa

-- The Kripke logical relation is "sandwiched" between
-- reflection and reification. This means that we should
-- be able to prove the following implications by induction
-- on types:

-- (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : T) ⇒ Γ ⊢ 𝓊 : T Ⓡ ↑ᵀ 𝓊̂
==↑-Ⓡ : ∀ {Γ : Γ} {T : Type} {𝓊 : Γ ⊢ T} {𝓊̂ : Ne↑ T}
      → (∀ {Γ′ : SystemT.Γ}
         → (Γ′≤Γ : Γ′ ≤ Γ)
         → Γ′≤Γ ≤⊢ 𝓊 ==↑ 𝓊̂)
        -------------------
      → 𝓊 Ⓡ (↑ᵀ 𝓊̂)

-- Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ′ : T
Ⓡ-==↓ : ∀ {Γ′ Γ : Γ} {T : Type} {t : Γ ⊢ T} {a : ⟦ T ⟧}
      → t Ⓡ a
        ---------------------
      → (Γ′≤Γ : Γ′ ≤ Γ)
      → Γ′≤Γ ≤⊢ t == ↓ᵀᵧ a

-- A consequence of the first implication is that
-- Γ , x:T ⊢ x Ⓡ ↑ᵀ (𝓍̂ Γ), which will be helpful for proving the
-- second implication
xⓇ↑ᵀ𝓍̂ : ∀ {Γ : Γ} {T : Type}
        -------------------------
      → ` `Z {Γ} {T} Ⓡ ↑ᵀ (𝓍̂ T Γ)

-- To prove the first implication, first we show that it always
-- holds for liftable neutral terms of type nat
==↑-Ⓡ {T = nat} pf Γ′≤Γ = pf Γ′≤Γ
-- Now, for liftable neutral terms of type S → T, we prove that
-- the relation holds for ↑ᵀ (𝓊̂ · ↓ˢ a)
==↑-Ⓡ {T = _ ⇒ _} {𝓊} {𝓊̂} pf {Γ′} Γ′≤Γ {s} {a} sⓇa =
  -- We prove the relation holds by using our induction
  -- hypothesis, so that our new goal is to prove that
  -- Γ″ ⊢ 𝓊 s  = (𝓊̂ · (↓ˢ a)) Γ″ : T
  -- for any Γ″ that is an extension of Γ′ (which itself
  -- extends Γ).
  ==↑-Ⓡ 𝓊·s==𝓊̂·↓ˢa
    where
      𝓊·s==𝓊̂·↓ˢa : ∀ {Γ″ : Γ}
                 → (Γ″≤Γ′ : Γ″ ≤ Γ′)
                 → Γ″≤Γ′ ≤⊢ (Γ′≤Γ ≤⊢ 𝓊) · s ==↑ 𝓊̂ ·↑ (↓ᵀ a)
      𝓊·s==𝓊̂·↓ˢa  {Γ″} Γ″≤Γ′
        -- Note that (𝓊̂ · (↓ˢ a)) Γ″ is equivalent to
        -- 𝓊̂(Γ″) · (↓ˢ a)(Γ″). First, we deconstruct 𝓊̂ (Γ″),
        -- using our given proof that it's definitionally
        -- equal to Γ″ ⊢ 𝓊 : S → T to both discard the case
        -- where 𝓊̂ (Γ″) is undefined and simplify our goal
        -- to proving that:
        --   Γ″ ⊢ 𝓊 · s = 𝓊″ · ↓ˢ a Γ″ : T
        -- (where 𝓊″ is 𝓊̂ lifted to the context Γ″)
        with 𝓊̂ Γ″           | pf (≤-trans Γ″≤Γ′ Γ′≤Γ)
      ... | inj₁ ⟨ 𝓊″ , _ ⟩ | 𝓊==𝓊″
        -- We also use the other implication we will prove,
        -- alongside the fact that s Ⓡ a, to have evidence
        -- that Γ″ ⊢ s : S is definitionally equal to
        -- ↓ˢ a Γ″
        with Ⓡ-==↓ sⓇa Γ″≤Γ′
      ... | s==↓ᵀᵧa =
        -- We can now use equational reasoning for
        -- definitional equality to prove the desired goal
        begin
          Γ″≤Γ′ ≤⊢ (Γ′≤Γ ≤⊢ 𝓊) · s
        ==⟨ app-compatible (≡→== (weaken-compose Γ″≤Γ′ Γ′≤Γ 𝓊)) refl ⟩
          (Γ″≤Γ ≤⊢ 𝓊) · (Γ″≤Γ′ ≤⊢ s)
        ==⟨ app-compatible 𝓊==𝓊″ refl ⟩
          𝓊″ · (Γ″≤Γ′ ≤⊢ s)
        ==⟨ app-compatible refl s==↓ᵀᵧa ⟩
          𝓊″ · ↓ᵀᵧ a
        ∎
        where
          Γ″≤Γ = ≤-trans Γ″≤Γ′ Γ′≤Γ

-- To prove the second implication, we proceed similarly
-- and first prove it for type nat. If the term is logically
-- related to zero, the implication holds immediately from
-- our given proof
Ⓡ-==↓ {T = nat} {a = zero} pf Γ′≤Γ with ↓ᵀ {nat} zero
... | _ = pf Γ′≤Γ
-- Otherwise, if the term is logically related to
-- a successor of a natural, our given proof
-- similarly leads to the implication
Ⓡ-==↓ {Γ} {T = nat} {t} {suc a} pf Γ′≤Γ
  with pf Γ′≤Γ
... | ⟨ n , ⟨ t==sn , n==a ⟩ ⟩
  with n==a ≤-refl
... | h rewrite [id]-identity {t = n} =
  begin
    Γ′≤Γ ≤⊢ t
  ==⟨ t==sn ⟩
    suc · n
  ==⟨ app-compatible refl (lemma {a = a} h) ⟩
    suc · ↓ᵀᵧ a
  ∎
  where
    -- For this case, we additionally need a lemma showing
    -- that if a term of type nat is definitionally
    -- equal to an object a of type ℕ̂ (i.e. a natural
    -- with embedded liftable neutrals), then it is
    -- definitionally equal to the reification of
    -- the object a. We can prove this by induction
    -- on a
    lemma : ∀ {Γ : SystemT.Γ} {n : Γ ⊢ nat} {a : ⟦ nat ⟧}
          → n ==ℕ̂ a
            ----------
          → n == ↓ᵀᵧ a
    lemma {a = zero} pf with ↓ᵀ {nat} zero
    ... | _ = pf
    lemma {Γ} {a = suc a} ⟨ n , ⟨ m==sn , n==a ⟩ ⟩
      with ↓ᵀ {nat} (suc a) | lemma {a = a} (n==a ≤-refl)
    ... | _                 | pf
      rewrite [id]-identity {t = n} = trans m==sn (app-compatible refl pf)
    lemma {Γ} {t} {ne 𝓊̂} pf
      with 𝓊̂ Γ | pf
    ... | inj₁ ⟨ 𝓊 , _ ⟩ | t≡𝓊 = t≡𝓊
-- Lastly, if the term is logically related to an
-- embedded liftable neutral, the implication also
-- holds immediately from our given proof
Ⓡ-==↓ {Γ′} {T = nat} {a = ne 𝓊̂} pf Γ′≤Γ
  with 𝓊̂ Γ′           | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩  | t≡𝓊     = t≡𝓊
-- For our inductive step, we prove the implication
-- for terms of type S → T. Our desired implication
-- is now:
--   Γ′ ⊢ t = ↓ᵀ f Γ′ : T
-- which, by definition, expands to:
--   Γ′ ⊢ t = λx. ↓ᵀ f a (Γ′ , x:S) : T
--     (where a = ↑ᵀ 𝓍̂ˢ Γ′)
Ⓡ-==↓ {Γ′} {T = S ⇒ _} {t} {f} pf Γ′≤Γ =
  -- We prove this by η expanding t to λx. t x and
  -- then using the compatibility rule for abstractions
  -- of definitional equality to simplify our goal to
  -- proving:
  --   Γ′ , x:S ⊢ t x = ↓ᵀ f a (Γ′, x:S)
  --
  -- Note that our inductive hypothesis is:
  --   t x Ⓡ f a implies t x = ↓ᵀ f a
  --
  -- This is exactly what we want to show, so now
  -- all we need is to prove that t x Ⓡ f a
  --
  -- Luckily, our given proof holds that t and f
  -- are logically related, which is equivalent
  -- to saying that if x Ⓡ a , then t x Ⓡ f a,
  -- reducing what we have to prove only to
  -- x Ⓡ a. We have been using "a" for simplicity,
  -- but a = ↑ᵀ 𝓍̂ˢ Γ′, and we are mutually proving
  -- that x Ⓡ ↑ᵀ 𝓍̂, so we use this lemma here
  -- to finish our proof.
  begin
    Γ′≤Γ ≤⊢ t
  ==⟨ η ⟩
    ƛ (S ↑⊢ Γ′≤Γ ≤⊢ t) · ` `Z
  ==⟨
    abs-compatible (
      begin
        (S ↑⊢ Γ′≤Γ ≤⊢ t) · ` `Z
      ==⟨ app-compatible subst-lemma refl ⟩
        (≤-, Γ′≤Γ ≤⊢ t) [ id ] · ` `Z
      ==⟨ Ⓡ-==↓ (pf (≤-, Γ′≤Γ) xⓇa) ≤-refl ⟩
        proj₁ (↓ᵀ (f a) (Γ′ , S))
      ∎
  )⟩
    proj₁ (↓ᵀ f Γ′)
  ∎
  where
    subst-lemma = ≡→== (≡-trans (incr-↑-≡ {t = t}) (≡-sym [id]-identity))
    a = ↑ᵀ {S} (𝓍̂ S Γ′)
    xⓇa = xⓇ↑ᵀ𝓍̂ {Γ′} {S}

-- Using our first implication, we
-- prove Γ , x:T ⊢ x : T Ⓡ ↑ᵀ 𝓍̂
xⓇ↑ᵀ𝓍̂ {_} {T} = ==↑-Ⓡ x==𝓍̂ where
  x==𝓍̂ : ∀ {Γ Γ′ : Γ}
       → (Γ′≤Γ,T : Γ′ ≤ (Γ , T))
       → Γ′≤Γ,T ≤⊢ ` `Z ==↑ 𝓍̂ T Γ
  x==𝓍̂ {Γ} {Γ′} pf
    with Γ′ ≤? (Γ , T)
  ... | no ¬pf = ¬pf pf
  ... | yes pf′
    with 𝓍̂ T Γ | ≤-pf-irrelevance pf pf′
  ... | _      | refl
    with ≤ᵨ pf′
  ...| _ , _  = refl

-- Before moving forward, we also want to show that rec Ⓡ ⟦rec⟧
-- (in other words, that our interpretation of rec is sound).
recⓇ⟦rec⟧ : ∀ {Γ : Γ} {T : Type} → rec {Γ} {T} Ⓡ ⟦rec⟧
recⓇ⟦rec⟧ Γ′≤Γ {z} pf Γ″≤Γ′ pf′ Γ‴≤Γ″ {s = n} {zero} pf″
  with pf″ ≤-refl
... | n==zero
  rewrite [id]-identity {t = n} =
  ==-Ⓡ (app-compatible refl (sym n==zero))
    (==-Ⓡ (sym β-rec-z) zⓇa)
    where
      Γ‴≤Γ′ = ≤-trans Γ‴≤Γ″ Γ″≤Γ′
      subst-lemma = ≡→== (≡-sym (weaken-compose Γ‴≤Γ″ Γ″≤Γ′ z))
      zⓇa = ==-Ⓡ subst-lemma (Ⓡ-ext {Γ′≤Γ = Γ‴≤Γ′} pf)

recⓇ⟦rec⟧ Γ′≤Γ {z} {az} pf Γ″≤Γ′ {s} {aₛ} pf′ Γ‴≤Γ″ {m} {suc aₙ} pf″
  with pf″ ≤-refl
... | ⟨ n , ⟨ m==saₙ , nⓇaₙ ⟩ ⟩
  rewrite [id]-identity {t = m} =
    ==-Ⓡ (app-compatible refl (sym m==saₙ))
      (==-Ⓡ (sym β-rec-s) s·n·recⓇaₛ·aₙ·⟦rec⟧)
  where
    subst-lemma₁ = [id]-identity {t = Γ‴≤Γ″ ≤⊢ s}
    subst-lemma₂ = [id]-identity {t = n}

    rec·z·s·n = (Γ‴≤Γ″ ≤⊢ (Γ″≤Γ′ ≤⊢ rec · z) · s) · n

    ih : rec·z·s·n Ⓡ ⟦rec⟧ az aₛ aₙ
    ih = recⓇ⟦rec⟧ Γ′≤Γ pf Γ″≤Γ′ {s = s} pf′ Γ‴≤Γ″ {s = n} {aₙ} nⓇaₙ

    s·n·recⓇaₛ·aₙ·⟦rec⟧ : (Γ‴≤Γ″ ≤⊢ s) · n · rec·z·s·n Ⓡ aₛ aₙ (⟦rec⟧ az aₛ aₙ)
    s·n·recⓇaₛ·aₙ·⟦rec⟧ with pf′ Γ‴≤Γ″ {n} nⓇaₙ ≤-refl ih
    ... | pf
      rewrite subst-lemma₁ | subst-lemma₂ = pf

recⓇ⟦rec⟧ {_} {T} Γ′≤Γ {z} {az} pf Γ″≤Γ′ {s} {aₛ} pf′ {Γ‴} Γ‴≤Γ″ {n} {ne 𝓊̂} pf″ =
  ==↑-Ⓡ rec==↑rec↑ where
    rec==↑rec↑ : ∀ {Γ⁗ : SystemT.Γ}
      → (Γ⁗≤Γ‴ : Γ⁗ ≤ Γ‴)
      → Γ⁗≤Γ‴ ≤⊢ (Γ‴≤Γ″ ≤⊢ (Γ″≤Γ′ ≤⊢ rec · z) · s) · n ==↑ rec↑ (↓ᵀ az) (↓ᵀ aₛ) 𝓊̂
    rec==↑rec↑ {Γ⁗} Γ⁗≤Γ‴
      with 𝓊̂ Γ⁗          | pf″ Γ⁗≤Γ‴
    ... | inj₁ ⟨ _ , _ ⟩ | n==𝓊 =
      app-compatible
        (app-compatible
          (app-compatible
            refl
            (z==↓ᵀaz))
          (trans
            η
            (abs-compatible
              (trans
                η
                (abs-compatible  s·x₁·x₂==↓ᵀas·↑ᵀ𝓍̂₁·↑ᵀ𝓍̂₂)))))
      n==𝓊
      where
        Γ‴≤Γ′ = ≤-trans Γ‴≤Γ″ Γ″≤Γ′
        Γ⁗≤Γ″ = ≤-trans Γ⁗≤Γ‴ Γ‴≤Γ″
        Γ⁗,nat≤Γ⁗ = ≤-, {T = nat} Γ⁗≤Γ″
        Γ⁗,nat,T≤Γ⁗ = ≤-, {T = T} Γ⁗,nat≤Γ⁗
        Γ⁗,nat,T≤Γ⁗,nat = ≤-, {T = T} (≤-refl {Γ⁗ , nat})

        subst-lemma₁ =
          ≡-sym (incr-↑-≡ {S = T} {σᵨ = _↑ᵨ {T = nat} (≤ᵨ Γ⁗≤Γ″)} {t = s})
        subst-lemma₂ =
          ≡-sym (incr-↑-≡ {S = nat} {σᵨ = ≤ᵨ Γ⁗≤Γ″} {t = s})
        subst-lemma₃ =
          ≡-sym (weaken-compose Γ⁗≤Γ‴ Γ‴≤Γ″ s)
        subst-lemma₄ = [id]-identity {t = T ↑⊢ nat ↑⊢ Γ⁗≤Γ‴ ≤⊢ Γ‴≤Γ″ ≤⊢ s}

        𝓍̂₁ = 𝓍̂ nat Γ⁗
        𝓍̂₂ = 𝓍̂ T (Γ⁗ , nat)

        s·x₁·x₂Ⓡaₛ·↑ᵀ𝓍̂₁↑ᵀ𝓍̂₂ =
          pf′ Γ⁗,nat≤Γ⁗ {s = ` `Z} {a = ↑ᵀ {nat} (𝓍̂ nat Γ⁗)} (xⓇ↑ᵀ𝓍̂ {Γ⁗} {nat})
            Γ⁗,nat,T≤Γ⁗,nat xⓇ↑ᵀ𝓍̂

        s·x₁·x₂==↓ᵀas·↑ᵀ𝓍̂₁·↑ᵀ𝓍̂₂ :
          (T ↑⊢ nat ↑⊢ Γ⁗≤Γ‴ ≤⊢ Γ‴≤Γ″ ≤⊢ s) · ` (`S `Z) · ` `Z ==
            proj₁ (↓ᵀ (aₛ (↑ᵀ 𝓍̂₁) (↑ᵀ 𝓍̂₂)) (Γ⁗ , nat , T))
        s·x₁·x₂==↓ᵀas·↑ᵀ𝓍̂₁·↑ᵀ𝓍̂₂
          with s·x₁·x₂Ⓡaₛ·↑ᵀ𝓍̂₁↑ᵀ𝓍̂₂
        ... | pf-Ⓡ
          rewrite subst-lemma₁ | subst-lemma₂ | subst-lemma₃
          with Ⓡ-==↓ pf-Ⓡ ≤-refl
        ... | pf-==↓
          rewrite subst-lemma₄ = pf-==↓

        subst-lemma₅ = ≡-sym (weaken-compose Γ⁗≤Γ‴ Γ‴≤Γ′ z)
        subst-lemma₆ = ≡-sym (weaken-compose Γ‴≤Γ″ Γ″≤Γ′ z)

        z==↓ᵀaz : Γ⁗≤Γ‴ ≤⊢ Γ‴≤Γ″ ≤⊢ Γ″≤Γ′ ≤⊢ z == proj₁ (↓ᵀ az Γ⁗)
        z==↓ᵀaz
          with Ⓡ-==↓ {Γ⁗} pf (≤-trans Γ⁗≤Γ‴ Γ‴≤Γ′)
        ... | pf
          rewrite subst-lemma₅ | subst-lemma₆ = pf

-- With that out of the way, having proved the lemma that
-- Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ : T, we have:
--   Γ ⊢ t : T Ⓡ a ⇒ Γ ⊢ t = ↓ᵀ a Γ : T
-- which is what we wanted our logical relation to imply,
-- so that we can then show that Γ ⊢ t : T Ⓡ a for a = ⟦t⟧ (↑ Γ)
--
-- For this, we will establish that Γ ⊢ t : T Ⓡ ⟦t⟧ (↑ Γ)
-- using the fundamental lemma of logical relations. First,
-- we will need to extend logical relations to include
-- substitutions and environments
_∥Ⓡ∥_ : ∀ {Γ Δ : Γ}
      → Γ ⊩ Δ
      → ⟦ Δ ⟧
      → Set

-- Similarly as for terms and values, a Kripe logical
-- relation between a parallel substitution and an
-- environment is defined inductively, though this time
-- by induction on the rules for parallel substitutions
-- instead of by induction on types

-- An empty substitution is always logically related to
-- an empty environment
∅ ∥Ⓡ∥ tt = ⊤

-- An extension to a substition (σ , s / x) is logically
-- related to an environment (ρ , a) if σ is logically
-- related to ρ and s is logically related to a
(σ , s) ∥Ⓡ∥ ⟨ ρ , a ⟩ = σ ∥Ⓡ∥ ρ × s Ⓡ a

infix 4 _∥Ⓡ∥_

-- A consequence of how substitutions and their logical
-- relation with environments are defined is that we
-- have that a logical relation for a shifted substitution
-- holds if the logical relation holds for the original
-- substitution (as the shifted terms will be irrelevant)
∥Ⓡ∥-↑ : ∀ {Γ Δ : Γ} {T : Type} {σᵨ : Γ ⊩ᵨ Δ} {ρ : ⟦ Δ ⟧}
      → substᵨ σᵨ ∥Ⓡ∥ ρ
      → substᵨ (_↑ᵨ {T = T} σᵨ) ∥Ⓡ∥ ρ
∥Ⓡ∥-↑ {σᵨ = ∅} pf = tt
∥Ⓡ∥-↑ {T = T} {σᵨ = _ , x} {⟨ _ , a ⟩} ⟨ pf , xⓇa ⟩ = ⟨ ∥Ⓡ∥-↑ pf , ↑⊢xⓇa ⟩
  where
    subst-lemma₁ = shift-var {S = T} {x = x} {σᵨ = idᵨ}
    subst-lemma₂ = rename-id {x = x}

    Γ,T≤Γ = ≤-, {T = T} ≤-refl

    ↑⊢xⓇa : ` (`S x) Ⓡ a
    ↑⊢xⓇa
      with Ⓡ-ext {Γ′≤Γ = Γ,T≤Γ} {t = ` x} xⓇa
    ... | pf
      rewrite subst-lemma₁ | subst-lemma₂ = pf

∥Ⓡ∥-ext : ∀ {Γ′ Γ Δ : Γ} {Γ′≤Γ : Γ′ ≤ Γ} {σ : Γ ⊩ Δ} {ρ : ⟦ Δ ⟧}
        → σ ∥Ⓡ∥ ρ
        → σ ∘ (weaken Γ′≤Γ) ∥Ⓡ∥ ρ
∥Ⓡ∥-ext {σ = ∅} x = tt
∥Ⓡ∥-ext {Γ′≤Γ = Γ′≤Γ} {σ , s} ⟨ σ∥Ⓡ∥ρ , sⓇa ⟩ =
  ⟨ ∥Ⓡ∥-ext {Γ′≤Γ = Γ′≤Γ} σ∥Ⓡ∥ρ , Ⓡ-ext {Γ′≤Γ = Γ′≤Γ} sⓇa ⟩

-- We introduce the semantic typing judgement
-- Γ ⊨ t : T as follows
_⊨_ : ∀ {T : Type} → (Γ : Γ) → Γ ⊢ T → Set
_⊨_ {T} Γ t =
  ∀ {Δ : SystemT.Γ} {σ : Δ ⊩ Γ} {ρ : ⟦ Γ ⟧}
  → σ ∥Ⓡ∥ ρ
    -------
  → t [ σ ] Ⓡ ⟦⊢ t ⟧ ρ

-- By induction on the typing judgement Γ ⊢ t : T,
-- we prove the semantic typing judgement Γ ⊨ t : T,
-- this is called the fundamental lemma of logical
-- relations
fundamental-lemma : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
                  → Γ ⊨ t
fundamental-lemma {t = zero} σ∥Ⓡ∥ρ _ = refl
fundamental-lemma {t = suc} σ∥Ⓡ∥ρ Δ′≤Δ {s} {a} pf {Δ″} Δ″≤Δ′ =
  ⟨ Δ″≤Δ′ ≤⊢ s , ⟨ refl , s==a ⟩ ⟩
  where
    s==a : ∀ {Δ‴ : Γ} → (Δ‴≤Δ″ : Δ‴ ≤ Δ″) → Δ‴≤Δ″ ≤⊢ Δ″≤Δ′ ≤⊢ s ==ℕ̂ a
    s==a Δ‴≤Δ″
      with pf (≤-trans Δ‴≤Δ″ Δ″≤Δ′)
    ... | pf
      rewrite weaken-compose Δ‴≤Δ″ Δ″≤Δ′ s = pf
fundamental-lemma {t = rec {T}} _ = recⓇ⟦rec⟧
fundamental-lemma {t = ` `Z} {σ = _ , _ } {⟨ _ , _ ⟩} ⟨ _ , xⓇa ⟩ = xⓇa
fundamental-lemma {t = ` (`S x)} {σ = _ , _} {⟨ _ , _ ⟩} ⟨ σ∥Ⓡ∥ρ , _ ⟩ =
  fundamental-lemma {t = ` x} σ∥Ⓡ∥ρ
fundamental-lemma {t = ƛ t} {σ = σ} {ρ} σ∥Ⓡ∥ρ Γ′≤Γ {s} {a} sⓇa =
  ==-Ⓡ (sym β-ƛ) t[σ′][s/x]Ⓡ⟦t⟧⟨ρ,a⟩
  where
    subst-lemma₁ =
      subst-compose {τ = id , s} {weaken Γ′≤Γ ↑ , ` `Z} {t [ σ ↑ , ` `Z ]}
    subst-lemma₂ =
     subst-compose {τ = ((weaken Γ′≤Γ ↑) ∘ (id , s)) , s} {σ ↑ , ` `Z} {t}

    t[σ′] = t [ σ ↑ , ` `Z ] [ weaken Γ′≤Γ ↑ , ` `Z ]

    subst-lemma₃ = subst-compose-↑ {τ = id} {weaken Γ′≤Γ} {s}
    subst-lemma₄ = subst-compose-↑ {τ = weaken Γ′≤Γ ∘ id} {σ} {s}
    subst-lemma₅ = id-compose-identity {σ = weaken Γ′≤Γ}

    σ″ = ((σ ↑) ∘ (((weaken Γ′≤Γ ↑) ∘ (id , s)) , s))

    σ″Ⓡρ : σ″  ∥Ⓡ∥ ρ
    σ″Ⓡρ rewrite subst-lemma₃ | subst-lemma₄ | subst-lemma₅ =
      ∥Ⓡ∥-ext {Γ′≤Γ = Γ′≤Γ} σ∥Ⓡ∥ρ

    t[σ′][s/x]Ⓡ⟦t⟧⟨ρ,a⟩ : t[σ′] [ s /x] Ⓡ ⟦⊢ t ⟧ ⟨ ρ , a ⟩
    t[σ′][s/x]Ⓡ⟦t⟧⟨ρ,a⟩ rewrite subst-lemma₁ | subst-lemma₂ =
        fundamental-lemma {t = t} ⟨ σ″Ⓡρ , sⓇa ⟩
fundamental-lemma {t = r · s} {σ = σ} σ∥Ⓡ∥ρ
  with fundamental-lemma {t = r} σ∥Ⓡ∥ρ | fundamental-lemma {t = s} σ∥Ⓡ∥ρ
... | Γ⊨r                              | Γ⊨s
  with Γ⊨r ≤-refl Γ⊨s
... | pf
  rewrite [id]-identity {t = r [ σ ]} = pf

-- For the identity substitution we have that Γ ⊢ id : Γ Ⓡ ↑Γ ,
-- which we prove using our lemma that Γ,x:T ⊢ x : T Ⓡ ↑ᵀ (𝓍ᵀ Γ),
-- and a few other lemmas
idⓇ↑Γ : ∀ {Γ : Γ}
       → id ∥Ⓡ∥ (↑Γ Γ)
idⓇ↑Γ {∅} = tt
idⓇ↑Γ {Γ , T} = ⟨ ∥Ⓡ∥-↑ {T = T} idⓇ↑Γ , xⓇ↑ᵀ𝓍̂ ⟩

-- With this fact, we arrive at the soundness of NbE:
soundness : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
          → t == nf t
soundness {Γ} {T} {t}
  -- Since the identity substition has that Γ ⊢ id : Γ Ⓡ ↑Γ,
  -- by the fundamental lemma we have that Γ ⊢ t Ⓡ ⟦t⟧ ↑Γ
  with fundamental-lemma {t = t} (idⓇ↑Γ {Γ})
... | tⓇ⟦t⟧↑Γ
  -- Using the lemma that logical relation implies definitional
  -- equality to the reified semantic object, we arrive at
  -- Γ ⊢ t = ↓ᵀᵧ ⟦ t ⟧ ↑Γ : T, which is what we want to show
  -- (i.e. Γ ⊢ t = nf(t) : T)
  with Ⓡ-==↓ tⓇ⟦t⟧↑Γ ≤-refl
... | t==↓ᵀᵧ⟦t⟧↑Γ
  rewrite [id]-identity {t = t [ id ]} | [id]-identity {t = t} = t==↓ᵀᵧ⟦t⟧↑Γ
