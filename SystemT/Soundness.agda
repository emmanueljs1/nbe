module Soundness where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import SystemT
open import NbE

{- Section 2.6 -- Soundness -}

-- We prove the soundness of normalization by proving
-- the definitional equality of a term and its normal form
-- i.e. Γ ⊢ t = nf(t) : T
--
-- For this, a logical relation Ⓡ is defined such that
-- it implies Γ ⊢ t = nf(t) : T

-- We start by defining a few functions for
-- the convenience of defining the relation

-- The first extends a well typed term in context Γ to its
-- corresponding well typed term in Γ′, an extension of Γ,
--
-- Formally, this represents the changing of contexts
-- used in the Kripe logical relation, e.g.
-- Γ ⊢ t : T ⇒ Γ′ ⊢ t : T
_ext-⊢_ : ∀ {Γ′ Γ : Γ} {T : Type} → Γ′ Γ-≤ Γ → Γ ⊢ T → Γ′ ⊢ T
pf ext-⊢ t = rename (lookup-Γ-≤ pf) t

infix 4 _ext-⊢_



-- We also define a few lemmas related to the operation:
-- the first lets us "collapse" a term extended twice
ext-⊢-collapse : ∀ {Γ₃ Γ₂ Γ₁ : Γ} {T : Type} {t : Γ₁ ⊢ T}
                 {Γ₃≤Γ₂ : Γ₃ Γ-≤ Γ₂} {Γ₂≤Γ₁ : Γ₂ Γ-≤ Γ₁}
               → (Γ₃≤Γ₁ : Γ₃ Γ-≤ Γ₁)
               → Γ₃≤Γ₂ ext-⊢ (Γ₂≤Γ₁ ext-⊢ t) def-≡ Γ₃≤Γ₁ ext-⊢ t
ext-⊢-collapse = {!!} -- TODO: prove

-- And this one allows us to extend definitional equality
-- to extensions of the context upon which the original
-- relation was established
def-≡-ext-⊢ : ∀ {Γ Γ′ : Γ} {T : Type} {Γ′≤Γ : Γ′ Γ-≤ Γ}
        {t t′ : Γ ⊢ T}
      → t def-≡ t′ → Γ′≤Γ ext-⊢ t def-≡ Γ′≤Γ ext-⊢ t′
def-≡-ext-⊢ = {!!} -- TODO: prove

-- The next function we define "lifts"
-- definitional equality over liftable neutrals
--
-- Formally, this represents the condition seen
-- in the Kripke logical relation:
--   Γ ⊢ 𝓊 = 𝓊̂(Γ) : T
-- or, equivalently in our syntax:
_def-≡↑_ : {Γ : Γ} {T : Type}
         → Γ ⊢ T
         → (𝓊̂ : Ne↑ T)
         → Set
_def-≡↑_ {Γ} t 𝓊̂ with 𝓊̂ Γ
... | inj₁ ⟨ 𝓊 , _ ⟩ =
      -- If the liftable neutral can be lifted to the
      -- context Γ, this is just definitional equality
      t def-≡ 𝓊
... | inj₂ _ =
      -- Otherwise, the proposition cannot be proven,
      -- as there is no lifted term in the context
      -- to compare a term to
      ⊥

infix 3 _def-≡↑_

-- The next function provides a shorthand for reifying
-- an interpretation of T then immediately applying a
-- context Γ
--
↓ᵀᵧ : ∀ {Γ : Γ} {T : Type} → (a : ⟦ T ⟧) → Γ ⊢ T
↓ᵀᵧ {Γ} a with ↓ᵀ a
... | a↑ = proj₁ (a↑ Γ)

-- The Kripe logical relation between a typed term Γ ⊢ T and a
-- value in ⟦T⟧, it is constructed by induction on types so
-- that it implies definitional equality
_Ⓡ_ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → ⟦ T ⟧ → Set

-- The relation defined over nats:
--   (t : Γ ⊢ nat) Ⓡ 𝓋̂ =
--     ∀ (Γ′ : Γ). Γ′ ≤ Γ → Γ′ ⊢ t = 𝓋̂(Γ) : nat
--
-- We slightly simplify the relation, as 𝓋̂ / 𝓋̂(Γ) are
-- a bit of an abuse of notation:
--   - For zero, there is no context Γ to lift to,
--     we are only concerned with definitional equality
_Ⓡ_ {_} {nat} t zero = t def-≡ zero

--   - For suc, we are only interested in the
--     underlying natural with embedded liftable neutrals,
--     so we further define the relation inductively
_Ⓡ_ {Γ} {nat} t (suc 𝓋̂) = ∃[ n ] n Ⓡ 𝓋̂ × t def-≡ (suc · n)

--   - For an embedded liftable neutral, the proposition
--     is a direct translation into our syntax
_Ⓡ_ {Γ₁} {nat} t (ne 𝓊̂) =
  ∀ {Γ₂ : Γ}
  → (Γ′ : Γ₂ Γ-≤ Γ₁)
    ----------------
  → Γ′ ext-⊢ t def-≡↑ 𝓊̂

-- The relation defined over functions:
--   (r : Γ ⊢ S ⇒ T) Ⓡ f =
--     ∀ (Γ′ : Γ). (s : Γ′ ⊢ S) Ⓡ a → Γ′ ⊢ r s Ⓡ f(a)
-- For this case, we can also provide a direct translation
-- into our syntax
_Ⓡ_ {Γ₁} {S ⇒ T} r f =
  ∀ {Γ₂ : Γ} {s : Γ₂ ⊢ S} {a : ⟦ S ⟧}
  → (Γ′ : Γ₂ Γ-≤ Γ₁)
  → s Ⓡ a
    --------------------
  → (Γ′ ext-⊢ r) · s Ⓡ f a

infix 4 _Ⓡ_

-- The Kripke logical relation is "sandwiched" between
-- reflection and reification. This means that we should
-- be able to prove the following implications by induction
-- on types:

-- (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : T) ⇒ Γ ⊢ 𝓊 : T Ⓡ ↑ᵀ 𝓊̂
def-≡↑→Ⓡ : ∀ {Γ₁ : Γ} {T : Type} {𝓊 : Γ₁ ⊢ T} {𝓊̂ : Ne↑ T}
          → (∀ {Γ₂ : Γ}
            → (Γ′ : Γ₂ Γ-≤ Γ₁)
            → Γ′ ext-⊢ 𝓊 def-≡↑ 𝓊̂)
            ----------------------
          → 𝓊 Ⓡ (↑ᵀ 𝓊̂)

-- t : Γ ⊢ T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ(a)(Γ′) : T
Ⓡ→def-≡ : ∀ {Γ₁ Γ₂ : Γ} {T : Type} {t : Γ₁ ⊢ T} {a : ⟦ T ⟧}
          → t Ⓡ a
            ----------------------
          → (Γ′ : Γ₂ Γ-≤ Γ₁)
          → Γ′ ext-⊢ t def-≡ ↓ᵀᵧ a

-- To prove the first implication, first we show that it always
-- holds for liftable neutral terms of type nat
def-≡↑→Ⓡ {T = nat} pf Γ′≤Γ = pf Γ′≤Γ
-- Now, for liftable neutral terms of type S ⇒ T, we prove that
-- the relation holds for ↑ᵀ (𝓊̂ · ↓ˢ a)
def-≡↑→Ⓡ {_} {T = _ ⇒ _} {𝓊} {𝓊̂} pf {Γ′} {s} {a} Γ′≤Γ sⓇa =
  -- We prove the relation holds by using our induction
  -- hypothesis, so that our new goal is to prove that
  -- Γ″ ⊢ 𝓊 · s is definitionally equal to 𝓊̂ · ↓ˢ a
  -- for any Γ″ that is an extension of Γ′ (which itself
  -- extends Γ).
  def-≡↑→Ⓡ 𝓊·s≡𝓊̂·↓ˢa
    where
      𝓊·s≡𝓊̂·↓ˢa : {Γ″ : Γ}
        → (Γ″≤Γ′ : Γ″ Γ-≤ Γ′)
        → Γ″≤Γ′ ext-⊢ (Γ′≤Γ ext-⊢ 𝓊) · s def-≡↑ 𝓊̂ ·↑ (↓ᵀ a)
      𝓊·s≡𝓊̂·↓ˢa  {Γ″} Γ″≤Γ′
        -- First, we deconstruct 𝓊̂ (Γ″), using our
        -- proof that it's definitionally equal
        -- to Γ″ ⊢ 𝓊 to both discard the case
        -- where 𝓊̂ (Γ″) is undefined and simplify
        -- our goal to proving that:
        -- Γ″ ⊢ 𝓊 · s = 𝓊″ · ↓ˢ a Γ″ : T
        -- (where 𝓊″ is 𝓊̂ lifted to the context Γ″)
        with 𝓊̂ Γ″ | pf (Γ-≤-trans Γ′≤Γ Γ″≤Γ′)
      ... | inj₁ ⟨ 𝓊″ , _ ⟩ | 𝓊≡𝓊″
        -- We also use the other implication we will prove,
        -- alongside the fact that s Ⓡ a, to
        -- show that Γ″ ⊢ s is definitionally equal to
        -- ↓ˢ a Γ″
        with Ⓡ→def-≡ sⓇa Γ″≤Γ′
      ... | s≡↓ᵀa =
        -- We can now use equational reasoning for
        -- definitional equality to prove the desired goal
        begin
          Γ″≤Γ′ ext-⊢ (Γ′≤Γ ext-⊢ 𝓊) · s
        def-≡⟨ ≡-app-compatible collapse ≡-refl ⟩
          (Γ″≤Γ ext-⊢ 𝓊) · (Γ″≤Γ′ ext-⊢ s)
        def-≡⟨ ≡-app-compatible 𝓊≡𝓊″ ≡-refl ⟩
          𝓊″ · (Γ″≤Γ′ ext-⊢ s)
        def-≡⟨ ≡-app-compatible ≡-refl s≡↓ᵀa ⟩
          𝓊″ · ↓ᵀᵧ a
        ∎
        where
          Γ″≤Γ = Γ-≤-trans Γ′≤Γ Γ″≤Γ′
          collapse = ext-⊢-collapse Γ″≤Γ

Ⓡ→def-≡ {T = nat} {t} {zero} t≡zero Γ′≤Γ with ↓ᵀ {nat} zero
... | _ = def-≡-ext-⊢ t≡zero
Ⓡ→def-≡ {T = nat} {t} {suc a} ⟨ n , ⟨ nⓇa , t≡sn ⟩ ⟩ Γ′≤Γ
  with ↓ᵀ {nat} (suc a)
... | _ =
  begin
    Γ′≤Γ ext-⊢ t
  def-≡⟨ def-≡-ext-⊢ t≡sn ⟩
    Γ′≤Γ ext-⊢ (suc · n)
  def-≡⟨ ≡-app-compatible ≡-refl (Ⓡ→def-≡ nⓇa Γ′≤Γ) ⟩
    suc · ↓ᵀᵧ a
  ∎
Ⓡ→def-≡ {_} {Γ′} {T = nat} {t} {ne 𝓊̂} pf Γ′≤Γ
  with 𝓊̂ Γ′          | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩ | t≡𝓊 = t≡𝓊
Ⓡ→def-≡ {Γ} {Γ′} {T = S ⇒ T} {t} {a = f} pf Γ′≤Γ = {!!}
-- the following proof works (albeit it has a small hole) but leads to
-- termination checks failing, keeping for reference until we figure out a
-- real proof:
--
--Ⓡ→def-≡ {Γ} {Γ′} {T = S ⇒ T} {t} {a = f} pf Γ′≤Γ
--  with ↑ᵀ {S} (𝓍̂ Γ′) | xⓇ↑ᵀ𝓍̂ {Γ′} {S}
--... | a              | xⓇa =
--  ≡-trans ≡-η (≡-abs-compatible (≡-trans {!!} (Ⓡ→def-≡ (pf (≤-, {T = S} Γ′≤Γ) xⓇa) ≤-refl)))

-- A consequence of the first implication is that
-- Γ , x:T ⊢ x Ⓡ ↑ᵀ (𝓍̂ Γ), as we show here:
xⓇ↑ᵀ𝓍̂ : ∀ {Γ : Γ} {T : Type}
     → ` `Z {Γ} {T} Ⓡ ↑ᵀ (𝓍̂ Γ)
xⓇ↑ᵀ𝓍̂ {_} {T} = def-≡↑→Ⓡ defeq where
  defeq : ∀ {Γ Γ′ : Γ}
        → (Γ′≤Γ,T : Γ′ Γ-≤ (Γ , T))
        → Γ′≤Γ,T ext-⊢ ` `Z def-≡↑ 𝓍̂ Γ
  defeq {Γ} {Γ′} pf
    with Γ′ Γ-≤? (Γ , T)
  ... | no ¬pf = ¬pf pf
  ... | yes pf′
    with 𝓍̂ {T} Γ | Γ-≤-uniq pf pf′
  ... | _        | refl            = ≡-refl

-- We will establish Γ ⊢ t : T Ⓡ ⟦t⟧ (↑ Γ) through the
-- fundamental lemma of logical relations, for this we
-- need to extend logical relations to include substitutions
-- and enviroments

-- An intrinsic substitution representation, i.e. σ : Γ ⊩ Δ,
-- we use ⊩ instead of ⊢ since that is already reserved
-- for typing judgements (and keep using ∥ for the "parallel"
-- in "parallel substitutions") for which we will be defining
-- similar logical relations
data _⊩_ : Γ → Γ → Set where
  ∅ : ∀ {Γ} → Γ ⊩ ∅

  _,_ : ∀ {Γ Δ : Γ} {S : Type}
        → Γ ⊩ Δ
        → Γ ⊢ S
          ---------
        → Γ ⊩ Δ , S

infix 4 _⊩_

-- Similarly as for terms and values, a Kripe logical
-- relation between a substitution and an environment
-- is defined inductively on substitutions
_∥Ⓡ∥_ : ∀ {Γ Δ : Γ}
      → Γ ⊩ Δ
      → ⟦ Δ ⟧
      → Set

infix 4 _∥Ⓡ∥_

∅ ∥Ⓡ∥ ρ = ⊤
(σ , s) ∥Ⓡ∥ ⟨ ρ , a ⟩ = σ ∥Ⓡ∥ ρ × s Ⓡ a

-- Before we formulate the fundamental lemma,
-- we introduce the operation t ∥[ σ ]∥ which allows
-- us to switch contexts
_∥[_]∥ : ∀ {Γ Δ : Γ} {T : Type}
     → Δ ⊢ T
     → Γ ⊩ Δ
       -----
     → Γ ⊢ T
t ∥[ ∅ ]∥ = Γ≤∅ ext-⊢ t
t ∥[ σ , s ]∥ = ((ƛ t) ∥[ σ ]∥) · s

-- We also introduce the semantic typing judgement
-- Γ ⊨ t : T as follows
_⊨_ : ∀ {T : Type} → (Γ : Γ) → Γ ⊢ T → Set
_⊨_ {T} Γ₁ t =
  ∀ {Δ : Γ} {σ : Δ ⊩ Γ₁} {ρ : ⟦ Γ₁ ⟧}
  → σ ∥Ⓡ∥ ρ
    -------
  → t ∥[ σ ]∥ Ⓡ ⊢⟦ t ⟧ ρ

-- This allows us to prove the fundamental lemma
-- of logical relations by induction on logical
-- relations
fundamental-lemma : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
                  → Γ ⊨ t
fundamental-lemma {t = zero} = {!!}
fundamental-lemma {t = suc} = {!!}
fundamental-lemma {t = rec} = {!!}
fundamental-lemma {t = ` x} = {!!}
fundamental-lemma {t = ƛ t} = {!!}
fundamental-lemma {t = t · t₁} = {!!}

-- We define a substitution that shifts
-- indices an arbitrary amount of times
-- to turn a context which extends
-- another context in the original context
↑ : ∀ {Γ′ Γ : Γ}
  → Γ′ Γ-≤ Γ
  → Γ′ ⊩ Γ
↑ {∅} ≤-refl = ∅
↑ {_ , _} ≤-refl = (↑ (≤-, ≤-refl)) , ` `Z
↑ {Γ′ , T} {Γ} (≤-, pf) with ↑ pf
... | ∅ = ∅
... | σ , s = ↑ (≤-, (invert-Γ-≤ pf)) , (≤-, ≤-refl ext-⊢ s)

-- Additionally, we define the identity substitution in terms
-- of the shifting substitution
id : ∀ {Γ : Γ} → Γ ⊩ Γ
id {∅} = ∅
id {Γ , _} = ↑ (≤-, ≤-refl) , (` `Z)

-- We have, using Γ,x:T ⊢ x : T Ⓡ ↑ᵀ (𝓍ᵀ Γ), that
-- Γ ⊢ id : Γ Ⓡ ↑Γ
idⓇ↑Γ : ∀ {Γ : Γ}
       → id ∥Ⓡ∥ (↑Γ Γ)
idⓇ↑Γ = {!!}

-- With this fact, we arrive at the soundness of NbE:
soundness : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
          → t def-≡ nf t
soundness {Γ} {T} {t}
  with fundamental-lemma {t = t} (idⓇ↑Γ {Γ})
... | pf
  with Ⓡ→def-≡ pf ≤-refl
... | pf = ≡-trans {!!} pf
