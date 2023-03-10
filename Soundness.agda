module Soundness where

open import Data.Unit using (⊤; tt)
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
_ext-⊢_ : ∀ {Γ′ Γ : Γ} {T : Type} → Γ′ ≤ Γ → Γ ⊢ T → Γ′ ⊢ T
pf ext-⊢ t = t [ weaken pf ]

infix 4 _ext-⊢_

-- A term extended twice can be "collapsed" to
-- a single extension
ext-⊢-collapse : ∀ {Γ₃ Γ₂ Γ₁ : Γ} {T : Type}
  → (Γ₃≤Γ₂ : Γ₃ ≤ Γ₂)
  → (Γ₂≤Γ₁ : Γ₂ ≤ Γ₁)
  → (t : Γ₁ ⊢ T)
  → Γ₃≤Γ₂ ext-⊢ (Γ₂≤Γ₁ ext-⊢ t) == (≤-trans Γ₃≤Γ₂ Γ₂≤Γ₁) ext-⊢ t
ext-⊢-collapse = {!!}

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
_==ℕ̂_ : {Γ : Γ} → Γ ⊢ nat → ⟦ nat ⟧ → Set
_==ℕ̂_ {Γ} t zero = t == zero
_==ℕ̂_ {Γ} t (suc 𝓋̂) = ∃[ n ] t == suc · n × n ==ℕ̂ 𝓋̂
_==ℕ̂_ {Γ} t (ne 𝓊̂) = t ==↑ 𝓊̂

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
--   (t : Γ ⊢ nat) Ⓡ 𝓋̂ =
--     ∀ (Γ′ : Γ). Γ′ ≤ Γ → Γ′ ⊢ t = 𝓋̂(Γ) : nat
_Ⓡ_ {Γ} {nat} t 𝓋̂ =
  ∀ {Γ′ : SystemT.Γ}
  → (Γ′≤Γ : Γ′ ≤ Γ)
  → Γ′≤Γ ext-⊢ t ==ℕ̂ 𝓋̂

-- The relation defined over functions:
--   Γ ⊢ r : S → T Ⓡ f =
--     ∀ (Γ′ : Γ). s : Γ′ ⊢ s : S Ⓡ a ⇒ Γ′ ⊢ r s : T Ⓡ f(a)
_Ⓡ_ {Γ} {S ⇒ T} r f =
  ∀ {Γ′ : SystemT.Γ} {s : Γ′ ⊢ S} {a : ⟦ S ⟧}
  → (Γ′≤Γ : Γ′ ≤ Γ)
  → s Ⓡ a
    -------------------------
  → (Γ′≤Γ ext-⊢ r) · s Ⓡ f a

infix 4 _Ⓡ_

-- The Kripke logical relation is "sandwiched" between
-- reflection and reification. This means that we should
-- be able to prove the following implications by induction
-- on types:

-- (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : T) ⇒ Γ ⊢ 𝓊 : T Ⓡ ↑ᵀ 𝓊̂
==→Ⓡ : ∀ {Γ : Γ} {T : Type} {𝓊 : Γ ⊢ T} {𝓊̂ : Ne↑ T}
      → (∀ {Γ′ : SystemT.Γ}
         → (Γ′≤Γ : Γ′ ≤ Γ)
         → Γ′≤Γ ext-⊢ 𝓊 ==↑ 𝓊̂)
        ----------------------
      → 𝓊 Ⓡ (↑ᵀ 𝓊̂)

-- Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ′ : T
Ⓡ→== : ∀ {Γ′ Γ : Γ} {T : Type} {t : Γ ⊢ T} {a : ⟦ T ⟧}
     → t Ⓡ a
       ---------------------
     → (Γ′≤Γ : Γ′ ≤ Γ)
     → Γ′≤Γ ext-⊢ t == ↓ᵀᵧ a

-- A consequence of the first implication is that
-- Γ , x:T ⊢ x Ⓡ ↑ᵀ (𝓍̂ Γ), which will be helpful for proving the
-- second implication
xⓇ↑ᵀ𝓍̂ : ∀ {Γ : Γ} {T : Type}
        -------------------------
      → ` `Z {Γ} {T} Ⓡ ↑ᵀ (𝓍̂ T Γ)

-- To prove the first implication, first we show that it always
-- holds for liftable neutral terms of type nat
==→Ⓡ {T = nat} pf Γ′≤Γ = pf Γ′≤Γ
-- Now, for liftable neutral terms of type S → T, we prove that
-- the relation holds for ↑ᵀ (𝓊̂ · ↓ˢ a)
==→Ⓡ {T = _ ⇒ _} {𝓊} {𝓊̂} pf {Γ′} {s} {a} Γ′≤Γ sⓇa =
  -- We prove the relation holds by using our induction
  -- hypothesis, so that our new goal is to prove that
  -- Γ″ ⊢ 𝓊 s  = (𝓊̂ · (↓ˢ a)) Γ″ : T
  -- for any Γ″ that is an extension of Γ′ (which itself
  -- extends Γ).
  ==→Ⓡ 𝓊·s==𝓊̂·↓ˢa
    where
      𝓊·s==𝓊̂·↓ˢa : ∀ {Γ″ : Γ}
        → (Γ″≤Γ′ : Γ″ ≤ Γ′)
        → Γ″≤Γ′ ext-⊢ (Γ′≤Γ ext-⊢ 𝓊) · s ==↑ 𝓊̂ ·↑ (↓ᵀ a)
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
        with Ⓡ→== sⓇa Γ″≤Γ′
      ... | s==↓ᵀᵧa =
        -- We can now use equational reasoning for
        -- definitional equality to prove the desired goal
        begin
          Γ″≤Γ′ ext-⊢ (Γ′≤Γ ext-⊢ 𝓊) · s
        ==⟨ app-compatible (ext-⊢-collapse Γ″≤Γ′ Γ′≤Γ 𝓊) refl ⟩
          (Γ″≤Γ ext-⊢ 𝓊) · (Γ″≤Γ′ ext-⊢ s)
        ==⟨ app-compatible 𝓊==𝓊″ refl ⟩
          𝓊″ · (Γ″≤Γ′ ext-⊢ s)
        ==⟨ app-compatible refl s==↓ᵀᵧa ⟩
          𝓊″ · ↓ᵀᵧ a
        ∎
        where
          Γ″≤Γ = ≤-trans Γ″≤Γ′ Γ′≤Γ

-- To prove the second implication, we proceed similarly
-- and first prove it for type nat. If the term is logically
-- related to zero, the implication holds immediately from
-- our given proof
Ⓡ→== {T = nat} {a = zero} pf Γ′≤Γ with ↓ᵀ {nat} zero
... | _ = pf Γ′≤Γ
-- Otherwise, if the term is logically related to
-- a successor of a natural, our given proof
-- similarly leads to the implication
Ⓡ→== {T = nat} {t} {suc a} pf Γ′≤Γ
  with pf Γ′≤Γ
... | ⟨ n , ⟨ t≡sn , n≡a ⟩ ⟩ =
  begin
    Γ′≤Γ ext-⊢ t
  ==⟨ t≡sn ⟩
    suc · n
  ==⟨ app-compatible refl (lemma {a = a} n≡a) ⟩
    suc · ↓ᵀᵧ a
  ∎
  where
    -- For this case, we additionally need a lemma showing
    -- that if a term of type nat is logically related
    -- to an object a of type ℕ̂ (i.e. a natural with
    -- embedded liftable neutrals), then it is
    -- definitionally equal to the reification of
    -- the object a. We can prove this by induction
    -- on the object of type ℕ̂
    lemma : ∀ {Γ : Γ} {n : Γ ⊢ nat} {a : ⟦ nat ⟧}
          → n ==ℕ̂ a
            ----------
          → n == ↓ᵀᵧ a
    lemma {a = zero} pf with ↓ᵀ {nat} zero
    ... | _ = pf
    lemma {a = suc a} ⟨ n , ⟨ m≡sn , n≡a ⟩ ⟩
      with ↓ᵀ {nat} (suc a) | lemma {a = a} n≡a
    ... | _                 | pf   =
      trans m≡sn (app-compatible refl pf)
    lemma {Γ} {t} {ne 𝓊̂} pf
      with 𝓊̂ Γ | pf
    ... | inj₁ ⟨ 𝓊 , _ ⟩ | t≡𝓊 = t≡𝓊
-- Lastly, if the term is logically related to an
-- embedded liftable neutral, the implication also
-- holds immediately from our given proof
Ⓡ→== {Γ′} {T = nat} {a = ne 𝓊̂} pf Γ′≤Γ
  with 𝓊̂ Γ′           | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩  | t≡𝓊     = t≡𝓊
-- For our inductive step, we prove the implication
-- for terms of type S → T. Our desired implication
-- is now:
--   Γ′ ⊢ t = ↓ᵀ f Γ′ : T
-- which, by definition, expands to:
--   Γ′ ⊢ t = λx. ↓ᵀ f a (Γ′ , x:S) : T
--     (where a = ↑ᵀ 𝓍̂ˢ Γ′)
Ⓡ→== {Γ′} {T = S ⇒ _} pf Γ′≤Γ
  with ↑ᵀ {S} (𝓍̂ S Γ′) | xⓇ↑ᵀ𝓍̂ {Γ′} {S}
... | a                | xⓇa =
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
  trans
    η
    (abs-compatible
      (trans
        (app-compatible {!!} refl)
        (Ⓡ→== (pf (≤-, {T = S} Γ′≤Γ) xⓇa) ≤-refl)))

-- Using our first implication, we
-- prove Γ , x:T ⊢ x : T Ⓡ ↑ᵀ 𝓍̂
xⓇ↑ᵀ𝓍̂ {_} {T} = ==→Ⓡ x==𝓍̂ where
  x==𝓍̂ : ∀ {Γ Γ′ : Γ}
       → (Γ′≤Γ,T : Γ′ ≤ (Γ , T))
       → Γ′≤Γ,T ext-⊢ ` `Z ==↑ 𝓍̂ T Γ
  x==𝓍̂ {Γ} {Γ′} pf
    with Γ′ ≤? (Γ , T)
  ... | no ¬pf = ¬pf pf
  ... | yes pf′
    with 𝓍̂ T Γ | ≤-uniq pf pf′
  ... | _      | refl
    with ≤ᵨ pf′
  ...| _ , x  = refl

-- We now have that Γ ⊢ t : T Ⓡ a ⇒ Γ ⊢ t = ↓ᵀ a Γ : T,
-- which is what we want to show for a = ⟦t⟧ (↑ Γ)
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

-- An empty substitution is always logically related to
-- an empty environment
∅ ∥Ⓡ∥ tt = ⊤

-- An extension to a substition (σ , s / x) is logically
-- related to an environment (ρ , a) if σ is logically
-- related to ρ and s is logically related to a
(σ , s) ∥Ⓡ∥ ⟨ ρ , a ⟩ = σ ∥Ⓡ∥ ρ × s Ⓡ a

infix 4 _∥Ⓡ∥_

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
fundamental-lemma = {!!}

-- For the identity substitution we have that Γ ⊢ id : Γ,
-- which we prove using our lemma that Γ,x:T ⊢ x : T Ⓡ ↑ᵀ (𝓍ᵀ Γ)
idⓇ↑Γ : ∀ {Γ : Γ}
       → id ∥Ⓡ∥ (↑Γ Γ)
idⓇ↑Γ {∅} = tt
idⓇ↑Γ {Γ , T} = {!!}

-- With this fact, we arrive at the soundness of NbE:
soundness : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
          → t == nf t
soundness {Γ} {T} {t}
  with fundamental-lemma {t = t} (idⓇ↑Γ {Γ})
... | pf
  with Ⓡ→== pf ≤-refl
... | pf                  =
  trans {!!} pf
