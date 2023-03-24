# Normalization by Evaulation

```agda
import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no)
open Eq using (_≡_; refl)

open import SystemT

module NbE where
```

Normalization by evaluation is the process of obtaining the normal
form of a term by evaluating it in a meta language (in our case, Agda).

Evaluating terms in System T in our meta language will require defining the interpretations of its types, contexts, and terms.

We use the following record to represent interpretations of types and contexts in System T, indicated by ⟦_⟧.
```agda
record Interpretation (D : Set) : Set₁ where
  field
    ⟦_⟧ : D → Set

open Interpretation {{...}} public
```

The thesis first introduces a more traditional interpretation of these,
but these definitions will need to be updated in our final implementation
of the NbE algorithm.

For types, we can interpret naturals in System T as ℕ, and functions in
System T as Agda functions, defined inductively on their types.

    ⟦ nat ⟧ = ℕ
    ⟦ S ⇒ T ⟧ = ⟦ S ⟧ → ⟦ T ⟧

An empty context is interpreted as the unit type, and an extension to
a context is defined inductively, with the extension itself being the
interpretation of the type the context is extended with.

    ⟦ ∅ ⟧ = ⊤
    ⟦ Γ , S ⟧ = ⟦ Γ ⟧ × ⟦ S ⟧

From now on, we will use the metavariable ρ is used to represent elements of ⟦ Γ ⟧ for a context Γ.

The interpretation of a variable expects the interpretation
of a context, and is essentially a lookup:

    ⟦ Γ ∋ x:T ⟧ (ρ ∈ ⟦Γ⟧) ∈ ⟦ T ⟧
    ⟦ Γ , T ∋ x:T ⟧ (ρ , a) = a
    ⟦ Γ , y:S ∋ x:T ⟧ (ρ , _) = ⟦ Γ ∋ x:T ⟧ ρ

The interpretation of a typed term expects the interpretation
of a context as well. It is more involed, so we only include
the rule for variables and abstractions:

    ⟦ Γ ⊢ t : T ⟧ (ρ ∈ ⟦Γ⟧) = ⟦ T ⟧
    ⟦ Γ ⊢ x : T ⟧ ρ = ⟦ Γ ∋ x:T ⟧ ρ
    ⟦ Γ ⊢ λx . t : S ⇒ T ⟧ ρ  a  = ⟦ Γ , x:S ⊢ t : T ⟧ (ρ , a)

As our final definition of interpretation will change, this is
only a rough sketch, but gives an idea of how we can evaluate terms
in Agda. For now, we only include the concrete interpretation of
a context Γ (generalized over any interpretation of types), as it will
remain unchanged.

```agda
instance
    -- We only include the concrete interpretation of a
    -- context Γ, generalized over any interpretation of
    -- types, to be used with the actual interpretation
    -- defined later
    ⟦Γ⟧ : {{_ : Interpretation Type}} → Interpretation Γ
    Interpretation.⟦ ⟦Γ⟧ ⟧ ∅ = ⊤
    Interpretation.⟦ ⟦Γ⟧ ⟧ (Γ , T) = ⟦ Γ ⟧ × ⟦ T ⟧
```

To motivate our algorithm, first we recognize that normalization by evaluation is,
intuitively, the evaulation of an expression with unknowns (e.g. variables) to
another, possibly simplified, expression with unknowns.

Because of this, we arrive at the first change to our interpretation of terms.
The interpretation of the base type nat is now terms of type nat in their
normal form -- after all, a variable of type nat is "blocked" and cannot be
evaluated any further. In other words, we now have:

    ⟦ nat ⟧ = terms of type nat in their normal form

From now on, normalized terms with unknowns will be referred to as neutral terms
(indicated by the metavariable 𝓊 for "unknown"), and normalized terms in general
will be referred to as normal terms (indicated by the metavariable 𝓋 for "value").

Additionally, while evaluation gives us the ability to normalize terms,
it also transforms them into our meta language. We want a way to return
to System T, which will be a function we will refer to as reification.
We will refer to its opposite, e.g. the transformation of a term in System T
into our meta language, as reflection.

The normal form of a typed term t in context Γ will be obtained by using
reflection and reification together. The following steps make up a sketch
of the algorithm:

  1) reflect the variables of the context Γ
     (all of which are neutral terms)
  2) interpret the value of the term using the environment
     of reflected variables
  3) "reify" the interpreted value of the term (i.e. returning
     it to a term in normal form)

Before we can actually define the algorithm, we need to formally introduce
normal and neutral terms in Agda, which we define mutually. The constructors
for these represent the different types of normal terms, and they are parametrized
by the terms themselves.

```agda
-- Neutral terms
data Ne (T : Type) (Γ : Γ) : Γ ⊢ T → Set
-- Normal Terms
data Nf : (T : Type) → (Γ : Γ) → Γ ⊢ T → Set
```

Neutral terms are normal terms in their blocked form. Variables are the "base
case" for blocked terms. Application on an unknown function to a normal term is
also blocked, as is recursion on an unknown natural.
blocked terms.
```agda
data Ne T Γ where
  ne-var : (x : Γ ∋ T)
           ------------
         → Ne T Γ (` x)

  ne-app : ∀ {S : Type} {𝓊 : Γ ⊢ S ⇒ T} {𝓋 : Γ ⊢ S}
         → Ne (S ⇒ T) Γ 𝓊
         → Nf S Γ 𝓋
           --------------
         → Ne T Γ (𝓊 · 𝓋)

  ne-rec : {𝓋z : Γ ⊢ T} {𝓋s : Γ ⊢ nat ⇒ T ⇒ T} {𝓊 : Γ ⊢ nat}
         → Nf T Γ 𝓋z
         → Nf (nat ⇒ T ⇒ T) Γ 𝓋s
         → Ne nat Γ 𝓊
           --------------------------
         → Ne T Γ (rec · 𝓋z · 𝓋s · 𝓊)
```

Normal terms are terms in their normal form. `zero`, and `suc` applied to a
normal term are normalized naturals. An abstraction whose body is normalized
is itself normalized, as is any neutral term.
```agda
data Nf where
  nf-zero : ∀ {Γ : Γ} → Nf nat Γ zero

  nf-suc : ∀ {Γ : Γ} {𝓋 : Γ ⊢ nat}
         → Nf nat Γ 𝓋
           ------------------
         → Nf nat Γ (suc · 𝓋)

  nf-abs : ∀ {S T : Type} {Γ : Γ} {𝓋 : Γ , S ⊢ T}
         → Nf T (Γ , S) 𝓋
           ------------------
         → Nf (S ⇒ T) Γ (ƛ 𝓋)

  nf-neutral : ∀ {T : Type} {Γ : Γ} {𝓊 : Γ ⊢ T}
             → Ne T Γ 𝓊
               --------
             → Nf T Γ 𝓊
```

With these defined, we can give a more formal (but still not final) sketch
of our algorithm:

    ⟦ nat ⟧ = Nf nat

    ↑ᵀ ∈ Ne T → ⟦ T ⟧
    ↑ⁿᵃᵗ 𝓊 = 𝓊
    ↑ˢ⃗ᵗ 𝓊 (a ∈ ⟦ S ⟧) = ↑ᵀ (𝓊 𝓋) , 𝓋 = ↓ˢ a
    
    ↓ᵀ ∈ ⟦ T ⟧ → Nf T
    ↓ⁿᵃᵗ 𝓋 = 𝓋
    ↓ˢ⃗ᵗ f = λx. ↓ᵀ (f(a)) , where a = ↑ᵀ x and x is "fresh"
    
    ↑Γ ∈ ⟦ Γ ⟧
    ↑∅ = tt
    ↑Γ,x:S = ↑Γ , ↑ˢ x
    
    nf(t) = ↓ᵀ (⟦ t ⟧ ↑Γ)

The algorithm takes a term, evaluates it in an environment of reflected
variables, and then reifies it back to System T. However, this sketch
has an immediate issue to figure out -- how to determine the freshness
condition for the variable x used when reifying at function type.

As we are using de Brujin indices, this has a simple solution: just extend
the context. However, there is no context anywhere in our definition
of reification, so what context do we extend with the fresh variable?
This is actually intentional, because of an issue that is more subtle:
after we reflect the variable, it may later be reified in a different
context than it was created.

To address this, we introduce liftable terms. These are terms that are
generalized over contexts, and can be applied to any context Γ.

An effect of this is that it could be that the resulting term is not
well defined. In fact, it will be the case that liftable neutral terms can
only be applied to extensions of the context under which they were created.
Because of this, liftable neutrals will need to return a placeholder value (tt)
for some contexts.

We append the up arrow ↑ for the liftable version of a System T construct, and
use 𝓋̂ and 𝓊̂ as the metavariables for liftable normal terms and neutral terms
respectively.
```agda
-- Liftable neutral term
Ne↑ : Type → Set
Ne↑ T = ∀ (Γ : Γ) → ∃[ t ] Ne T Γ t ⊎ ⊤

-- Liftable normal term
Nf↑ : Type → Set
Nf↑ T = ∀ (Γ : Γ) → ∃[ t ] Nf T Γ t
```

Application of liftable terms is overloaded, i.e. (𝓊̂ 𝓋̂)(Γ) = 𝓊̂(Γ)𝓋̂(Γ)
```agda
_·↑_ : ∀ {S T : Type} → Ne↑ (S ⇒ T) →  Nf↑ S → Ne↑ T
(𝓊̂ ·↑ 𝓋̂) Γ    with  𝓊̂ Γ |          𝓋̂ Γ
... | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩ | ⟨ 𝓋 , pf-𝓋 ⟩ =
      -- Note that we need to provide proof
      -- that our resulting lifted term is
      -- a neutral term as well
      inj₁ ⟨ 𝓊 · 𝓋 , ne-app pf-𝓊 pf-𝓋 ⟩
... | inj₂ tt           | _ = inj₂ tt
```

Since normalization by evaluation will need to be
over liftable terms, the concrete interpretation of
the base type nat will in the end be naturals with embedded liftable
neutrals, which we can now finally define in Agda, along with the
interpretation of types.
```agda
data ℕ̂ : Set where
  zero : ℕ̂
  suc : ℕ̂ → ℕ̂
  ne : Ne↑ nat → ℕ̂

instance
  ⟦Type⟧ : Interpretation Type
  Interpretation.⟦ ⟦Type⟧ ⟧ nat = ℕ̂
  Interpretation.⟦ ⟦Type⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧
```

With this, we begin the most important part
of normalization by evaluation, the reflection
and reification functions. These are mutually
recursive, and will be defined inductively
on the type T

```agda
-- Reflection of neutral terms of type T into
-- semantic objects in ⟦T⟧
↑ᵀ : {T : Type} → Ne↑ T → ⟦ T ⟧

-- Reification of semantic objects in ⟦T⟧ into
-- normal terms of type T
↓ᵀ : {T : Type} → ⟦ T ⟧ → Nf↑ T

-- ↑ᴺ - Reflection of neutral terms of type nat into ⟦nat⟧ (i.e. ℕ̂),
--      here we just embed the liftable neutral
```

As was the case in the sketch of the algorithm, the reflection
of a liftable neutral of type nat into the metalanguage (i.e. into
a term ℕ̂) is just the liftable neutral itself, embedded with the
ne constructor.
```agda
↑ᵀ {nat} 𝓊̂ = ne 𝓊̂
```

As for the reflection of neutral terms of type S ⇒ T into ⟦S⟧ → ⟦T⟧,
we reify a semantic object in ⟦S⟧ and then reflect the neutral term
resulting from the application of the reified object to the original
neutral term. Here, we use the liftable application operation we
defined earlier.
```agda
↑ᵀ {S ⇒ T} 𝓊̂ a = ↑ᵀ (𝓊̂ ·↑ 𝓋̂) where 𝓋̂ = ↓ᵀ a
```

For the reification of semantic objects of type ⟦nat⟧,
which are our naturals with embedded liftable neutrals (ℕ̂),
we define the following helper function.
```agda
↓ℕ̂ : ⟦ nat ⟧ → Nf↑ nat
↓ℕ̂ zero = (λ _ → ⟨ zero , nf-zero ⟩)
```

For the successor case, we reify the successor into a liftable
successor function (suc↑) applied to the reification of the argument
to the successor function
```agda
↓ℕ̂ (suc n) = suc↑ (↓ℕ̂ n) where
  suc↑ : Nf↑ nat → Nf↑ nat
  suc↑ 𝓋̂ Γ with 𝓋̂ Γ
  ... | ⟨ 𝓋 , pf ⟩ = ⟨ suc · 𝓋 , nf-suc pf ⟩
```

In the case of an embedded liftable neutral, we use `zero` as a
fallback if the liftable neutral is undefined at the context.
Our proof of soundness later will be proof that this fallback is not
necessary in our algorithm.
```agda
↓ℕ̂ (ne 𝓊̂) Γ with 𝓊̂ Γ
... | inj₁ ⟨ 𝓊 , pf ⟩ = ⟨ 𝓊 , nf-neutral pf ⟩
... | inj₂ tt         = ⟨ zero , nf-zero ⟩
```

For reification at function type, we will need the following
function which creates a "fresh" variable for a context Γ.
Really, this is just the de Brujin index 0 for a context Γ , x:S.
This will be a liftable variable that can be used in a context
that is an extension of Γ , x:S (and is undefined otherwise).
```
𝓍̂ : (S : Type) → Γ → Ne↑ S
𝓍̂ S Γ Γ′ with Γ′ ≤? (Γ , S)
... | no _ = inj₂ tt
... | yes pf with ≤ᵨ pf
  -- The variable x in the extended context Γ′ can
  -- be accessed through the renaming between Γ′ and
  -- Γ , S
... | _ , x = inj₁ ⟨ ` x , ne-var x ⟩
```

For our reification function, we reuse ↓ℕ̂ at type nat.
```agda
↓ᵀ {nat} = ↓ℕ̂
```

For the eification of semantic objects of type ⟦S → T⟧ (which are functions
of type ⟦S⟧ → ⟦T⟧), the resulting normal term is an abstraction over the
reification of the function applied to the reflection of the bound variable,
for which we use 𝓍̂
 ```agda
↓ᵀ {S ⇒ T} f Γ with ↓ᵀ (f a) (Γ , S) where a = ↑ᵀ (𝓍̂ S Γ)
... | ⟨ 𝓋 , pf ⟩ = ⟨ ƛ 𝓋 , nf-abs pf ⟩
```

With these two functions in place, we can define the reflection of a context
Γ into an environment. This will be the reflected environment over which a typed
term in the context Γ will be evaluated.
```agda
↑Γ : ∀ (Γ : Γ) → ⟦ Γ ⟧
↑Γ ∅ = tt
↑Γ (Γ , T) = ⟨ ↑Γ Γ  , ↑ᵀ (𝓍̂ T Γ) ⟩
```

We also need to use reflection and reification to
define the interpretation of primitive recursion in
System T, which must work with liftable neutrals (as
our interpretation of nat now has them embedded)
```agda
rec↑ : ∀ {T : Type} → Nf↑ T → Nf↑ (nat ⇒ T ⇒ T) → Ne↑ nat → Ne↑ T
rec↑ 𝓋̂z 𝓋̂s 𝓊̂ Γ with 𝓊̂ Γ
... | inj₂ tt = inj₂ tt
... | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩
      with 𝓋̂z Γ      | 𝓋̂s Γ
... | ⟨ 𝓋z , pf-𝓋z ⟩ | ⟨ 𝓋s , pf-𝓋s ⟩ =
  inj₁ ⟨ rec · 𝓋z · 𝓋s · 𝓊 , ne-rec pf-𝓋z pf-𝓋s pf-𝓊 ⟩

⟦rec⟧ : ∀ {T : Type} → ⟦ T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T ⟧
⟦rec⟧ z s zero = z
⟦rec⟧ z s (suc n) = s n (⟦rec⟧ z s n)
⟦rec⟧ {T} z s (ne 𝓊̂) =
  ↑ᵀ (rec↑ 𝓋̂z 𝓋̂s 𝓊̂) where 𝓋̂z = ↓ᵀ z ; 𝓋̂s = ↓ᵀ s
```

Now that we have a concrete interpretation of types,
and an interpretation for primitive recursion,
we can define the corresponding interpretations of
the lookup and typing judgements.
```agda
⟦_∋Γ⟧ : ∀ {Γ : Γ} {T : Type} → Γ ∋ T → ⟦ Γ ⟧ → ⟦ T ⟧
⟦_∋Γ⟧ {Γ , T} `Z ⟨ _ , a ⟩ = a
⟦_∋Γ⟧ {Γ , T} (`S x) ⟨ ρ , _ ⟩ = ⟦ x ∋Γ⟧ ρ

⟦⊢_⟧ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → ⟦ Γ ⟧ → ⟦ T ⟧
⟦⊢ zero ⟧ _ = zero
⟦⊢ suc ⟧ _ = suc
⟦⊢ rec ⟧ _ = ⟦rec⟧
⟦⊢ ` x ⟧ = ⟦ x ∋Γ⟧
⟦⊢ ƛ t ⟧ ρ a = ⟦⊢ t ⟧ ⟨ ρ , a ⟩
⟦⊢ r · s ⟧ ρ = ⟦⊢ r ⟧ ρ (⟦⊢ s ⟧  ρ)
```

Finally, the algorithm for normalization by evaluation is as follows
```agda
nbe : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → ∃[ t ] Nf T Γ t
nbe {Γ} t = ↓ᵀ (⟦⊢ t ⟧ (↑Γ Γ)) Γ

nf : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → Γ ⊢ T
nf t with nbe t
... | ⟨ t′ , _ ⟩ = t′
```

And here we have some examples of the algorithm in action, reusing our
examples from [SystemT](./SystemT.lagda.md)

```agda
-- normal form of (λx. x) zero is zero
nf-ex1 : nf ex1 ≡ zero
nf-ex1 with ex1
... | _ = refl

-- normal form of suc ((λx. x) zero) is suc zero
nf-ex2 : nf ex2 ≡ (suc · zero)
nf-ex2 with ex2
... | _ = refl

-- normal form of x:nat, y:nat ⊢ suc ((λz. suc y) x)
-- is x:nat, y:nat ⊢ suc (suc y)
nf-ex3 : nf ex3 ≡ (suc · (suc · ` (`Z)))
nf-ex3 with ex3
... | _ = refl
```

As for the soundness properties we want from this algorithm:
  - `Γ ⊢ nf(t) : T` (well-typedness)
      We are using an intrinsically typed
      representation of terms, so this property is
      given to us automatically

  - `⟦ nf(t) ⟧ = ⟦ t ⟧` (preservation of meaning)
      We will prove this in the following section
      using definitional equality [Soundness](./Soundness.lagda.md)

  - `nf(nf(t)) = nf(t)` (idempotency)
      This follows directly from the preservation of
      meaning and completeness properties of the algorithm:

      By the soundness property of preservation of meaning,
      we have `Γ ⊢ nf t = t : T`, which implies `nf (nf t) = nf(t)`
      by completeness

For proving the completeness property of NbE,
our goal is to prove that two programs with the
same meaning (i.e. definitionally equal) have the
same normal form:

    Γ ⊢ t = t′ : T implies nf(t) = nf(t′)

We can prove this using some equational reasoning
paired with the definitional equality of two
terms impliying they are semantically equal
(included as a postulate for now)

```agda
postulate
  ==→⟦≡⟧ : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T} {ρ : ⟦ Γ ⟧}
         → t == t′
         → ⟦⊢ t ⟧ ρ ≡ ⟦⊢ t′ ⟧ ρ

completeness : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T}
             → t == t′
             → nf t ≡ nf t′
completeness {Γ} t==t′ rewrite ==→⟦≡⟧ {ρ = ↑Γ Γ} t==t′ = refl
```
