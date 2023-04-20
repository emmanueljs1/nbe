---
title: "Normalization by Evaluation"
author: Emmanuel Suárez Acevedo
---

This is a formalization of Chapter 2 of Andreas Abel's habilitation thesis, "Normalization by Evaluation: Dependent Types and Impredicativity". [@nbe].

We start off by defining the language that we will
use to showcase normalization by evaluation, System T,
as is done in Section 2.1.
```agda
import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open Eq using (_≡_; refl)
open Eq using (refl; _≡_) renaming (sym to ≡-sym; trans to ≡-trans)

module NbE where
```

It has natural numbers, higher-order functions, and
primitive recursion. We will define it with intrinsic
typing, and use a de Brujin index representation
for variables.

We start off with the types of tha language: naturals
and functions.
```agda
data Type : Set where
  nat : Type
  _⇒_ : ∀ (S T : Type) → Type

infixr 7 _⇒_

_≟Tp_ : ∀ (S T : Type) → Dec (S ≡ T)
nat       ≟Tp nat                                  = yes refl
nat       ≟Tp (S ⇒ T)                              = no λ()
(S₁ ⇒ T₁) ≟Tp nat                                  = no λ()
(S₁ ⇒ T₁) ≟Tp (S₂ ⇒ T₂) with S₁ ≟Tp S₂ | T₁ ≟Tp T₂
...                        | no ¬pf    | no _      = no λ{refl → ¬pf refl}
...                        | no ¬pf    | yes _     = no λ{refl → ¬pf refl}
...                        | yes _     | no ¬pf    = no λ{refl → ¬pf refl}
...                        | yes refl  | yes refl  = yes refl
```

We continue with typing contexts, defined inductively
with the empty context, and extensions to contexts. As
we are using a de Brujin index representation, there
are no names when extending contexts (and really they
are just lists of types).
```agda
data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

infixl 5 _,_

_≟Ctx_ : ∀ (Γ′ Γ : Ctx) → Dec (Γ′ ≡ Γ)
∅       ≟Ctx ∅                                  = yes refl
∅       ≟Ctx (_ , _)                            = no λ()
(_ , _) ≟Ctx ∅                                  = no λ()
(Γ′ , S) ≟Ctx (Γ , T) with Γ′ ≟Ctx Γ | S ≟Tp T
...                      | no ¬pf    | no _     = no λ{refl → ¬pf refl}
...                      | no ¬pf    | yes _    = no λ{refl → ¬pf refl}
...                      | yes _     | no ¬pf   = no λ{refl → ¬pf refl}
...                      | yes refl  | yes refl = yes refl
```

We also define a relation detailing when one context is the
extension of another, this is introduced formally in a later
section but will be useful throughout. A context is an extension
of itself, and given that one context Γ′ extends another context
Γ, the first can be extended further and the relation will still hold.
```agda
data _≤_ : Ctx → Ctx → Set where
  ≤-id : ∀ {Γ : Ctx} → Γ ≤ Γ

  ≤-ext : ∀ {Γ Γ′ : Ctx} {T : Type}
        → Γ′ ≤ Γ
          ----------
        → Γ′ , T ≤ Γ

infix 4 _≤_

Γ≤∅ : ∀ {Γ : Ctx} → Γ ≤ ∅
Γ≤∅ {∅} = ≤-id
Γ≤∅ {Γ , _} with Γ≤∅ {Γ}
...            | pf      = ≤-ext pf

_≤?_ : ∀ (Γ′ Γ : Ctx) → Dec (Γ′ ≤ Γ)
∅        ≤? ∅          = yes ≤-id
∅        ≤? (_ , _)    = no λ()
(_ , _)  ≤? ∅          = yes Γ≤∅
(Γ′ , T) ≤? Γ@(_ , _)
  with (Γ′ , T) ≟Ctx Γ
...  | yes refl        = yes ≤-id
...  | no Γ′≢Γ
  with Γ′ ≤? Γ
...  | yes pf          = yes (≤-ext pf)
...  | no ¬pf          = no λ where
                           ≤-id → Γ′≢Γ refl
                           (≤-ext pf) → ¬pf pf
```

We also introduce a lookup judgement for
contexts, which corresponds to a de Brujin
index.
```agda
data _∋_ : Ctx → Type → Set where
  `Z : ∀ {Γ : Ctx} {T : Type}
        ---------
      → Γ , T ∋ T

  `S_ : ∀ {Γ : Ctx} {S T : Type}
      → Γ ∋ T
        ---------
      → Γ , S ∋ T

infix 4 _∋_
```

Terms in our language are defined with an intrinsically
typed represenation, such that a term t of type Γ ⊢ T is
the term `Γ ⊢ t : T` itself. The language has the constants `zero`,
`suc` (as a curried constant),`rec` (a curried constant
as well), variables, abstractions, and application.

For clarity we will not use an intrinsically typed de Brujin
representation when talking about terms (e.g. the variable ` `Z
will be talked about as `Γ , x:T ⊢ x : T`)
```agda
data _⊢_ (Γ : Ctx) : Type → Set where
  zero : Γ ⊢ nat

  suc : Γ ⊢ nat ⇒ nat

  rec  : ∀ {T : Type}
         ---------------------------------
       → Γ ⊢ (T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T)

  `_ : ∀ {S : Type}
     → Γ ∋ S
       -----
     → Γ ⊢ S

  ƛ_ : ∀ {S T : Type}
     → Γ , S ⊢ T
       ---------
     → Γ ⊢ S ⇒ T

  _·_ : ∀ {S T : Type}
      → Γ ⊢ S ⇒ T
      → Γ ⊢ S
        ---------
      → Γ ⊢ T

infix 4 _⊢_
infix 5 ƛ_
infixl 7 _·_
infix 9 `_
```

We can define some sample programs in the language
using these constructors:
```agda
-- λx. x
ex0 : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T ⇒ T
ex0 = ƛ ` (`Z)

-- (λx. x) zero
ex1 = ex0 · zero {∅}

-- suc ((λx. x) zero)
ex2 = suc · ex1

-- x:nat, y:nat ⊢ suc ((λz. suc y) x)
ex3 : ∅ , nat , nat ⊢ nat
ex3 = suc · ((ƛ suc · ` (`S `Z)) · ` (`S `Z))
```

Now that we have defined our language, we are almost ready
to start describing an algorithm for normalization by
evaluation. However, to prove the soundness of this algorithm,
we will need to define two more basic language constructs:
substitutions and equality.

We expect the following soundness properties for a
normalization algorithm nf(t) that produces a normal form
for a typed term `Γ ⊢ t : T`:

  - `Γ ⊢ nf(t) : T` (well-typedness of normal form)
  - `⟦ nf(t) ⟧ = ⟦ t ⟧` (preservation of meaning)
  - `nf(nf(t)) = nf(t)` (idempotency)

For preservation of meaning, our interpretations of
functional terms are functions, whose equality is
undecidable. However, in STLC, we have that two terms
are βη-equivalent iff their interpretationss are equal.
So, we wish to define an extension of βη-equivalence
for System T s.t. it implies equal interpretations
(thus making the proposition `⟦ nf(t) ⟧ = ⟦ t ⟧` decidable).

To define our extension of βη-equivalence, we begin by
defining substitution (which we will use to define β-reductions
and η-expansions).

Substitution for System T is defined using the rules for
parallel substitution and the rule for the application
of a substitution as they are introduced in section 2.6.

A parallel substitution `Γ ⊢ σ : Δ` provides a well-typed term in Γ
to substitute for each variable in the context Δ.

We use ⊩ instead of ⊢ since that is already reserved
for typing judgements (and keep using ∥ for the "parallel"
in "parallel substitutions" for operationsions related
to this type).
```agda
data Sub : Ctx → Ctx → Set where
  ∅ : ∀ {Γ} → Sub Γ ∅

  _,_ : ∀ {Γ Δ : Ctx} {S : Type}
        → Sub Γ Δ
        → Γ ⊢ S
          ---------
        → Sub Γ (Δ , S)
```

Before defining the application of a substitution
`Γ ⊢ t [ σ ] : `T, we introduce renaming.

Renaming is a specialized substitution where
we can only substitute variables with other
variables (i.e. a renaming `Γ ⊢ σᵣ : Δ` provides
a variable in Γ to replace for every variable in Δ).

It is necessary to first to define renaming substitutions
so that termination is guaranteed for our operations.
```agda
data Ren : Ctx → Ctx → Set where
  ∅ : ∀ {Γ : Ctx} → Ren Γ ∅

  _,_ : ∀ {Γ Δ : Ctx} {S : Type}
      → Ren Γ Δ
      → Γ ∋ S
        -------------
      → Ren Γ (Δ , S)
```

We can use a renaming substitution to convert
lookup judgements (i.e. rename variables). In fact, this
is the operation that we need to define separately to
guarantee termination of the application of a substitution.
```agda
rename : ∀ {Γ Δ : Ctx} {T : Type}
       → Δ ∋ T
       → Ren Γ Δ
         -------
       → Γ ∋ T
rename `Z     (ρ , x) = x
rename (`S x) (ρ , _) = rename x ρ
```

We define parallel substitutions and renaming substitutions
with the previous rules so that we can define a shifting operation
over them. Shifting a renaming substitution shifts all indices
in the renaming by one -- in other words, given a renaming between Γ
and Δ, we can create a renaming between Γ , T and Δ.

We will use this to extend a renaming under a binder.
```agda
_↑ᵣ : ∀ {Γ Δ : Ctx} {T : Type}
    → Ren Γ Δ
      -------------
    → Ren (Γ , T) Δ
∅ ↑ᵣ       = ∅
(σᵣ , x) ↑ᵣ = σᵣ ↑ᵣ , `S x

infix 6 _↑ᵣ
```

With this operation in place, we can define the application of a renaming
substitution to rebase a term from a context Δ to a context Γ, this is done
by using the renaming substitution to replace all variables used in the term by
their corresponding variables in Γ
```agda
_[_]ᵣ : ∀ {Γ Δ : Ctx} {T : Type}
        → Δ ⊢ T
        → Ren Γ Δ
          -------
        → Γ ⊢ T
zero [ _ ]ᵣ = zero
suc [ _ ]ᵣ = suc
rec [ _ ]ᵣ = rec
` `Z [ _ , x ]ᵣ = ` x
` `S x [ σᵣ , _ ]ᵣ = ` x [ σᵣ ]ᵣ
(ƛ t) [ σᵣ ]ᵣ = ƛ t [ σᵣ ↑ᵣ , `Z ]ᵣ
(r · s) [ σᵣ ]ᵣ = r [ σᵣ ]ᵣ · s [ σᵣ ]ᵣ

infix 8 _[_]ᵣ
```

We also define a few "primitive" renamings that will be convenient for general
substitutions:

The identity and incrementing renaming, defined mutually. The identity
renaming leaves all variables unchanged, while the incrementing renaming
increments all variables (which are really just indices) by 1

```agda
mutual
  ren-id : ∀ {Γ : Ctx} → Ren Γ Γ
  ren-id {∅} = ∅
  ren-id {Γ , T} = ren-incr , `Z

  ren-incr : ∀ {Γ : Ctx} {T : Type} → Ren (Γ , T) Γ
  ren-incr = ren-id ↑ᵣ
```

A renaming between a context Γ′ and Γ,
where Γ′ is an extension of Γ. This renaming
is really a series of shifts based on
how many extensions to Γ the context Γ′
contains.

```agda
ren-≤ : ∀ {Γ′ Γ : Ctx} → Γ′ ≤ Γ → Ren Γ′ Γ
ren-≤ ≤-id = ren-id
ren-≤ (≤-ext pf) = (ren-≤ pf) ↑ᵣ
```

Since a renaming is really just a specialized substitution,
we can transform any renaming substitution into a parallel
substitution
```agda
subst-ren : ∀ {Γ Δ : Ctx} → Ren Γ Δ → Sub Γ Δ
subst-ren ∅ = ∅
subst-ren (σᵣ , x) = subst-ren σᵣ , ` x
```

We can now use our renaming substitutions to build out
parallel substitutions and their operations, such that
their operations are guaranteed to terminate.

Similarly as for renaming substitutions, we define a shifting
operation for parallel substitutions, to be used for extending
a substitution under a binder.
```agda
_↑ : ∀ {Γ Δ : Ctx} {T : Type}
      → Sub Γ Δ
        -------------
      → Sub (Γ , T) Δ
∅ ↑       = ∅
(σ , s) ↑ = σ ↑ , s [ ren-incr ]ᵣ

infix 6 _↑
```

Now, we can define the application of a parallel substitution
`Γ ⊢ σ : Δ` to a term `Δ ⊢ t : T` (e.g. `t [ σ ]`)
```agda
_[_] : ∀ {Γ Δ : Ctx} {T : Type}
     → Δ ⊢ T
     → Sub Γ Δ
       -------
     → Γ ⊢ T
zero [ _ ] = zero
suc [ _ ] = suc
rec [ _ ] = rec
` `Z [ _ , x ] = x
` `S x [ σ , _ ] = ` x [ σ ]
(ƛ t) [ σ ] = ƛ (t [ σ ↑ , ` `Z ])
(r · s) [ σ ] = r [ σ ] · s [ σ ]

infix 8 _[_]
```

Substitutions can also be composed, by applying
a substitution `Γ₁ ⊢ τ : Ctx₂` to every term in a
substitution `Γ₂ ⊢ σ : Ctx₃`
```agda
_∘_ : ∀ {Γ₁ Γ₂ Γ₃ : Ctx} → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₂ → Sub Γ₁ Γ₃
∅       ∘ _ = ∅
(σ , s) ∘ τ = (σ ∘ τ) , s [ τ ]
```

We will want a weakening substitution, that allows us
to weaken a well typed term in Γ to a context Γ′ that
extends Γ.

Really, this substitution is the renaming substitution
between extended contexts
```agda
weaken : ∀ {Γ′ Γ : Ctx}
       → Γ′ ≤ Γ
         --------
       → Sub Γ′ Γ
weaken pf = subst-ren (ren-≤ pf)
```

For convenience, we will also want some shorthand for
applying a weakening substitution to a term
```agda
_≤⊢_ : ∀ {Γ′ Γ : Ctx} {T : Type} → Γ′ ≤ Γ → Γ ⊢ T → Γ′ ⊢ T
pf ≤⊢ t = t [ weaken pf ]

infixr 5 _≤⊢_
```

Additionally, we define an identity and incrementing
parallel substitution, which are simply the identity and
incrementing renaming substitutions
```agda
subst-id : ∀ {Γ : Ctx} → Sub Γ Γ
subst-id = subst-ren ren-id

subst-incr : ∀ {Γ : Ctx} {T : Type} → Sub (Γ , T) Γ
subst-incr = subst-ren ren-incr
```

The incrementing substitution will be used to establish
η-equivalence, we will also benfit from some shorthand for
its application to a term
```agda
_↑⊢_ : ∀ {Γ : Ctx} {T : Type} → (S : Type) → Γ ⊢ T → Γ , S ⊢ T
_ ↑⊢ t = t [ subst-incr ]

infixr 5 _↑⊢_
```

To establish β-equivalence, we define an operation for
substituting the first free variable in a term `Γ , x:S ⊢ t : T`
with a term `Γ ⊢ s : S` (i.e. `t [ s / x ]`), which is really
shorthand for `t [ id , s / x ]`
```agda
_[_/x] : ∀ {Γ : Ctx} {S T : Type}
  → Γ , T ⊢ S
  → Γ ⊢ T
    ---------
  → Γ ⊢ S
s [ t /x] =  s [ subst-id , t ]

infix 8 _[_/x]
```

With these defined, we can introduce a new relation between two
terms: definitional equality. In the thesis, this is
written as `Γ ⊢ t = t′ : T`, we will use t == t′ in Agda

The relation is written such that the definitional equality
of two terms implies the equality of their interpretations
(`Γ ⊢ t = t′ : T` iff `⟦ t ⟧ = ⟦ t′ ⟧`); it is the extension of
Βη-equivalence for System T suggested earlier

We will use this relation to prove the soundness property
of preservation of meaning for NbE (i.e. `⟦ nf(t) ⟧ = ⟦ t ⟧`)
```agda
data _==_ : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → Γ ⊢ T → Set where

  -- Computation rules
  β-rec-z : ∀ {Γ : Ctx} {T : Type}
              {z : Γ ⊢ T}
              {s : Γ ⊢ nat ⇒ T ⇒ T}
              -----------------------
            → rec · z · s · zero == z

  β-rec-s : ∀ {Γ : Ctx} {T : Type}
      {z : Γ ⊢ T}
      {s : Γ ⊢ nat ⇒ T ⇒ T}
      {n : Γ ⊢ nat}
      ----------------------------------------------------
    → rec · z · s · (suc · n) == s · n · (rec · z · s · n)

  β-ƛ : ∀ {Γ : Ctx} {S T : Type}
          {t : Γ , S ⊢ T}
          {s : Γ ⊢ S}
          ----------------------
        → (ƛ t) · s == t [ s /x]

  -- Function extensionality, i.e. Γ ⊢ t = Γ ⊢ λx. t x : S ⇒ T
  η : ∀ {Γ : Ctx} {S T : Type}
        {t : Γ ⊢ S ⇒ T}
        ----------------------
      → t == ƛ (S ↑⊢ t) · ` `Z

  -- Compatibility rules
  --
  -- Note that we do not need a rule for constants and variables as
  -- is given in the thesis as we are using an intrinsically typed
  -- representation, so refl catches all of these cases
  abs-compatible : ∀ {Γ : Ctx} {S T : Type} {t t′ : Γ , S ⊢ T}
                   → t == t′
                     -----------
                   → ƛ t == ƛ t′

  app-compatible : ∀ {Γ : Ctx} {S T : Type}
                     {r r′ : Γ ⊢ S ⇒ T} {s s′ : Γ ⊢ S}
                   → r == r′
                   → s == s′
                     ----------------
                   → r · s == r′ · s′

  -- Equivalence rules
  refl : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
           ------
         → t == t

  sym : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
        → t == t′
          -------
        → t′ == t

  trans : ∀ {Γ : Ctx} {T : Type} {t₁ t₂ t₃ : Γ ⊢ T}
          → t₁ == t₂
          → t₂ == t₃
            --------
          → t₁ == t₃

infix 3 _==_
```

For the clarity of some of our proofs, it will also be helpful to
have the ability to use equational reasoning with respect to
definitional equality.
```agda
module ==-Reasoning where
  infix  1 begin_
  infixr 2 _==⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
    → t == t′
      ---------
    → t == t′
  begin pf = pf

  _==⟨_⟩_ : ∀ {Γ : Ctx} {T : Type} {t₂ t₃ : Γ ⊢ T}
    → (t₁ : Γ ⊢ T)
    → t₁ == t₂
    → t₂ == t₃
      -----
    → t₁ == t₃
  t₁ ==⟨ t₁≡t₂ ⟩ t₂≡t₃  =  trans t₁≡t₂ t₂≡t₃

  _∎ : ∀ {Γ : Ctx} {T : Type} → (t : Γ ⊢ T)
      -----
    → t == t
  t ∎  =  refl

open ==-Reasoning public
```

Now, we are ready to start defining the algorithm for normalization by
evaluation. Normalization by evaluation is the process of obtaining the normal
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
    ⟦Γ⟧ : {{_ : Interpretation Type}} → Interpretation Ctx
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
data Ne (T : Type) (Γ : Ctx) : Γ ⊢ T → Set
-- Normal Terms
data Nf : (T : Type) → (Γ : Ctx) → Γ ⊢ T → Set
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
  nf-zero : ∀ {Γ : Ctx} → Nf nat Γ zero

  nf-suc : ∀ {Γ : Ctx} {𝓋 : Γ ⊢ nat}
         → Nf nat Γ 𝓋
           ------------------
         → Nf nat Γ (suc · 𝓋)

  nf-abs : ∀ {S T : Type} {Γ : Ctx} {𝓋 : Γ , S ⊢ T}
         → Nf T (Γ , S) 𝓋
           ------------------
         → Nf (S ⇒ T) Γ (ƛ 𝓋)

  nf-neutral : ∀ {T : Type} {Γ : Ctx} {𝓊 : Γ ⊢ T}
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
    
    ↑ᶜᵗˣ ∈ ⟦ Γ ⟧
    ↑∅ = tt
    ↑ᶜᵗˣ,x:S = ↑ᶜᵗˣ , ↑ˢ x
    
    nf(t) = ↓ᵀ (⟦ t ⟧ ↑ᶜᵗˣ)

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
Ne↑ T = ∀ (Γ : Ctx) → ∃[ t ] Ne T Γ t ⊎ ⊤

-- Liftable normal term
Nf↑ : Type → Set
Nf↑ T = ∀ (Γ : Ctx) → ∃[ t ] Nf T Γ t
```

Application of liftable terms is overloaded, i.e. (𝓊̂ 𝓋̂)(Γ) = 𝓊̂(Γ)𝓋̂(Γ)
```agda
_·↑_ : ∀ {S T : Type} → Ne↑ (S ⇒ T) →  Nf↑ S → Ne↑ T
(𝓊̂ ·↑ 𝓋̂) Γ with 𝓊̂ Γ               |          𝓋̂ Γ
...           | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩ | ⟨ 𝓋 , pf-𝓋 ⟩ =
      -- Note that we need to provide proof
      -- that our resulting lifted term is
      -- a neutral term as well
      inj₁ ⟨ 𝓊 · 𝓋 , ne-app pf-𝓊 pf-𝓋 ⟩
...           | inj₂ tt           | _            = inj₂ tt
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
  suc↑ 𝓋̂ Γ =
    let ⟨ 𝓋 , pf ⟩ = 𝓋̂ Γ in
    ⟨ suc · 𝓋 , nf-suc pf ⟩
```

In the case of an embedded liftable neutral, we use `zero` as a
fallback if the liftable neutral is undefined at the context.
Our proof of soundness later will be proof that this fallback is not
necessary in our algorithm.
```agda
↓ℕ̂ (ne 𝓊̂) Γ with 𝓊̂ Γ
...            | inj₁ ⟨ 𝓊 , pf ⟩ = ⟨ 𝓊 , nf-neutral pf ⟩
...            | inj₂ tt         = ⟨ zero , nf-zero ⟩
```

For reification at function type, we will need the following
function which creates a "fresh" variable for a context Γ.
Really, this is just the de Brujin index 0 for a context `Γ , x:S`.
This will be a liftable variable that can be used in a context
that is an extension of `Γ , x:S` (and is undefined otherwise).
```
𝓍̂ : (S : Type) → Ctx → Ne↑ S
𝓍̂ S Γ Γ′
  with Γ′ ≤? (Γ , S)
...  | no _          = inj₂ tt
...  | yes pf
  -- The variable x in the extended context Γ′ can
  -- be accessed through the renaming between Γ′ and
  -- Γ , S
  with ren-≤ pf
...  | _ , x         = inj₁ ⟨ ` x , ne-var x ⟩
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
↓ᵀ {S ⇒ T} f Γ =
  let ⟨ 𝓋 , pf ⟩ = ↓ᵀ (f a) (Γ , S) in
  ⟨ ƛ 𝓋 , nf-abs pf ⟩
  where a = ↑ᵀ (𝓍̂ S Γ)
```

With these two functions in place, we can define the reflection of a context
Γ into an environment. This will be the reflected environment over which a typed
term in the context Γ will be evaluated.
```agda
↑ᶜᵗˣ : ∀ (Γ : Ctx) → ⟦ Γ ⟧
↑ᶜᵗˣ ∅       = tt
↑ᶜᵗˣ (Γ , T) = ⟨ ↑ᶜᵗˣ Γ  , ↑ᵀ (𝓍̂ T Γ) ⟩
```

We also need to use reflection and reification to
define the interpretation of primitive recursion in
System T, which must work with liftable neutrals (as
our interpretation of nat now has them embedded)
```agda
rec↑ : ∀ {T : Type} → Nf↑ T → Nf↑ (nat ⇒ T ⇒ T) → Ne↑ nat → Ne↑ T
rec↑ 𝓋̂z 𝓋̂s 𝓊̂ Γ with 𝓊̂ Γ
... | inj₂ tt = inj₂ tt
... | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩ =
  let ⟨ 𝓋z , pf-𝓋z ⟩ = 𝓋̂z Γ in
  let ⟨ 𝓋s , pf-𝓋s ⟩ = 𝓋̂s Γ in
  inj₁ ⟨ rec · 𝓋z · 𝓋s · 𝓊 , ne-rec pf-𝓋z pf-𝓋s pf-𝓊 ⟩

⟦rec⟧ : ∀ {T : Type} → ⟦ T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T ⟧
⟦rec⟧ z s zero       = z
⟦rec⟧ z s (suc n)    = s n (⟦rec⟧ z s n)
⟦rec⟧ {T} z s (ne 𝓊̂) =
  ↑ᵀ (rec↑ 𝓋̂z 𝓋̂s 𝓊̂) where 𝓋̂z = ↓ᵀ z ; 𝓋̂s = ↓ᵀ s
```

Now that we have a concrete interpretation of types,
and an interpretation for primitive recursion,
we can define the corresponding interpretations of
the lookup and typing judgements.
```agda
⟦_∋Γ⟧ : ∀ {Γ : Ctx} {T : Type} → Γ ∋ T → ⟦ Γ ⟧ → ⟦ T ⟧
⟦_∋Γ⟧ {Γ , T} `Z ⟨ _ , a ⟩     = a
⟦_∋Γ⟧ {Γ , T} (`S x) ⟨ ρ , _ ⟩ = ⟦ x ∋Γ⟧ ρ

⟦⊢_⟧ : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → ⟦ Γ ⟧ → ⟦ T ⟧
⟦⊢ zero ⟧ _  = zero
⟦⊢ suc ⟧ _   = suc
⟦⊢ rec ⟧ _   = ⟦rec⟧
⟦⊢ ` x ⟧     = ⟦ x ∋Γ⟧
⟦⊢ ƛ t ⟧ ρ a = ⟦⊢ t ⟧ ⟨ ρ , a ⟩
⟦⊢ r · s ⟧ ρ = ⟦⊢ r ⟧ ρ (⟦⊢ s ⟧  ρ)
```

Finally, the algorithm for normalization by evaluation is as follows
```agda
nbe : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → ∃[ t ] Nf T Γ t
nbe {Γ} t = ↓ᵀ (⟦⊢ t ⟧ (↑ᶜᵗˣ Γ)) Γ

nf : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → Γ ⊢ T
nf t = let ⟨ t′ , _ ⟩ = nbe t in t′
```

And here we have some examples of the algorithm in action, reusing our
examples from [SystemT](./SystemT.lagda.md)

```agda
-- normal form of (λx. x) zero is zero
nf-ex1 : nf ex1 ≡ zero
nf-ex1 with ex1
...       | _   = refl

-- normal form of suc ((λx. x) zero) is suc zero
nf-ex2 : nf ex2 ≡ (suc · zero)
nf-ex2 with ex2
...       | _   = refl

-- normal form of x:nat, y:nat ⊢ suc ((λz. suc y) x)
-- is x:nat, y:nat ⊢ suc (suc y)
nf-ex3 : nf ex3 ≡ (suc · (suc · ` (`Z)))
nf-ex3 with ex3
...       | _   = refl
```

As for the soundness properties we want from this algorithm:
  - `Γ ⊢ nf(t) : T` (well-typedness)
      We are using an intrinsically typed
      representation of terms, so this property is
      given to us automatically

  - `⟦ nf(t) ⟧ = ⟦ t ⟧` (preservation of meaning)
      We will prove this in the following section
      using definitional equality

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
  ==→⟦≡⟧ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {ρ : ⟦ Γ ⟧}
         → t == t′
         → ⟦⊢ t ⟧ ρ ≡ ⟦⊢ t′ ⟧ ρ

completeness : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
             → t == t′
             → nf t ≡ nf t′
completeness {Γ} t==t′ rewrite ==→⟦≡⟧ {ρ = ↑ᶜᵗˣ Γ} t==t′ = refl
```

<!--

```agda
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
```

-->


# Soundness

We prove the soundness property of preservation of meaning of NbE
(i.e. `⟦ nf(t) ⟧ = ⟦ t ⟧`), which we just call soundness here for brevity,
by proving the definitional equality of a term and its normal form:

    Γ ⊢ t = nf(t) : T

which expands to:

    Γ ⊢ t = ↓ᵀ a Γ, where a = ⟦ t ⟧ ↑Γ

For this, a logical relation `t Ⓡ a` is defined such that
it implies `Γ ⊢ t = ↓ᵀ a Γ : T`.

For defining the relation in Agda, we will need some functions first. The first
"lifts" definitional equality over liftable neutrals. Formally, this represents the condition `Γ ⊢ 𝓊 = 𝓊̂(Γ) : T`, or equivalently in Agda:
```agda
_==↑_ : {Γ : Ctx} {T : Type} → Γ ⊢ T → Ne↑ T → Set
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
```

We also provide shorthand for reifying the interpretation of a term t
and then immediately applying a context Γ (we use lowercase γ as our
subscript as Γ is not a valid subscript)
```agda
↓ᵀᵧ : ∀ {Γ : Ctx} {T : Type} → (a : ⟦ T ⟧) → Γ ⊢ T
↓ᵀᵧ {Γ} a with ↓ᵀ a
... | a↑ = proj₁ (a↑ Γ)
```

With these, we can begin to introduce the Kripe logical relation `Γ ⊢ t : T Ⓡ a`
between a typed term `Γ ⊢ t : T` and a value `a ∈ ⟦ T ⟧`. The logical relation
will be defined inductively on types. At type nat, the relation is defined as:

    Γ : nat Ⓡ 𝓋̂ ⇔ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = 𝓋̂(Γ′) : nat

For Agda's termination checking, we have to define the logical relation at type
nat separately, which we do so in the form of Ⓝ:
```agda
_Ⓝ_ : ∀ {Γ : Ctx} → Γ ⊢ nat → ⟦ nat ⟧ → Set
```

We define Ⓝ mutually with ==ℕ̂, a relation representing
the condition `Γ′ ⊢ t = 𝓋̂(Γ′) : nat`, which lifts definitional equality to
be over naturals with embedded liftable neutrals

```agda
_==ℕ̂_ : ∀ {Γ : Ctx} → Γ ⊢ nat → ⟦ nat ⟧ → Set

_Ⓝ_ {Γ} n 𝓋̂ =
  ∀ {Γ′ : Ctx}
  → (Γ′≤Γ : Γ′ ≤ Γ)
    ---------------
  → Γ′≤Γ ≤⊢ n ==ℕ̂ 𝓋̂

infix 4 _Ⓝ_
```

For `zero`, the ==ℕ̂ relation is a simple definitional equality
judgement:
```agda
_==ℕ̂_ {Γ} t zero = t == zero
```
However, for our recursive case (suc 𝓋̂), the definition is a bit
more involved. We want the term to be definitionally equal to `suc · n`
such that n is logically related to 𝓋̂, a condition stronger than ==ℕ̂,
as it holds for all extensions of the context -- this is why we need
to define ==ℕ̂ mutually with Ⓝ. We want our recursive condition to be
stronger to have an easier time with the embedded liftable neutrals
```agda
_==ℕ̂_ {Γ} t (suc 𝓋̂) = ∃[ n ] t == suc · n × n Ⓝ 𝓋̂
```
For an embedded liftable neutral, the relation is the
lifted definitional equality defined earlier
```agda
_==ℕ̂_ {Γ} t (ne 𝓊̂) = t ==↑ 𝓊̂

infix 3 _==ℕ̂_
```

With these in place, we can start defining the logical
relation Ⓡ itself by induction on types, using Ⓝ for
the base type nat
```agda
_Ⓡ_ : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → ⟦ T ⟧ → Set

_Ⓡ_ {Γ} {nat} t 𝓋̂ = t Ⓝ 𝓋̂
```

For function types, the relation is defined as:
    Γ ⊢ r : S → T Ⓡ f ⇔ ∀ Γ′ ≤ Γ. Γ′ ⊢ s : S Ⓡ a ⇒ Γ′ ⊢ r s : T Ⓡ f(a)
```agda
_Ⓡ_ {Γ} {S ⇒ T} r f =
  ∀ {Γ′ : Ctx}
  → (Γ′≤Γ : Γ′ ≤ Γ)
  → ∀ {s : Γ′ ⊢ S} {a : ⟦ S ⟧}
  → s Ⓡ a
    ----------------------
  → (Γ′≤Γ ≤⊢ r) · s Ⓡ f a

infix 4 _Ⓡ_
```

A result of defining our Kripe logical relation in terms
of definitional equality is that the relation is transitive
with respect to definitional equality
```agda
==-Ⓡ-trans : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {a : ⟦ T ⟧}
           → t == t′
           → t Ⓡ a
             -------
           → t′ Ⓡ a
==-Ⓡ-trans {T = nat} {a = zero} t==t′ pf Γ′≤Γ =
  trans (sym (==-subst t==t′)) (pf Γ′≤Γ)
==-Ⓡ-trans {T = nat} {a = suc a} t==t′ pf Γ′≤Γ
  with pf Γ′≤Γ
... | ⟨ n , ⟨ t==sn , n==a ⟩ ⟩ =
  ⟨ n , ⟨ trans (sym (==-subst t==t′)) t==sn , n==a ⟩ ⟩
==-Ⓡ-trans {T = nat} {a = ne 𝓊̂} t==t′ pf {Γ′} Γ′≤Γ
  with 𝓊̂ Γ′          | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩ | t==𝓊 =
  trans (sym (==-subst t==t′)) t==𝓊
==-Ⓡ-trans {T = S ⇒ T} t==t′ pf Γ′≤Γ sⓇa =
  ==-Ⓡ-trans (app-compatible (==-subst t==t′) refl) (pf Γ′≤Γ sⓇa)
```

Additionally, because we have defined the relation so that its implication
holds for all extensions of a context, we can "weaken" the logical relation
`Γ ⊢ t : T Ⓡ a` for all `Γ′ ≤ Γ`, having that `Γ′ ⊢ t : T Ⓡ a` holds as well
```agda
Ⓡ-weaken : ∀ {Γ′ Γ : Ctx} {T : Type} {Γ′≤Γ : Γ′ ≤ Γ} {t : Γ ⊢ T} {a : ⟦ T ⟧}
      → t Ⓡ a
      → Γ′≤Γ ≤⊢ t Ⓡ a
Ⓡ-weaken {T = nat} {Γ′≤Γ} {t} pf Γ″≤Γ′
  rewrite weaken-compose Γ″≤Γ′ Γ′≤Γ t = pf (≤-trans Γ″≤Γ′ Γ′≤Γ)
Ⓡ-weaken {T = S ⇒ T} {Γ′≤Γ} {t} pf Γ″≤Γ′ sⓇa
  rewrite weaken-compose Γ″≤Γ′ Γ′≤Γ t = pf (≤-trans Γ″≤Γ′ Γ′≤Γ) sⓇa
```

The Kripke logical relation is "sandwiched" between
reflection and reification -- to arrive at the logical
relation between a term and a semantic object, the
semantic object must be a reflection of a liftable neutral
that is definitionally equal to the term. Likewise,
if a logical relation holds between a term and a semantic
object, then the term must be definitionally equal
to the reification of that semantic object.

This is intentional, as these results will be exactly
what we will need to prove the soundness of NbE. We
formalize them with the following implications, which
we will prove mutually (as reflection and reification
are themselves defined mutually) by induction on types.

Our first implication is:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : T) ⇒ Γ ⊢ 𝓊 : T Ⓡ ↑ᵀ 𝓊̂

which we can now formalize in Agda with our definitions
```agda
==↑-Ⓡ : ∀ {Γ : Ctx} {T : Type} {𝓊 : Γ ⊢ T} {𝓊̂ : Ne↑ T}
      → (∀ {Γ′ : Ctx}
         → (Γ′≤Γ : Γ′ ≤ Γ)
         → Γ′≤Γ ≤⊢ 𝓊 ==↑ 𝓊̂)
        -------------------
      → 𝓊 Ⓡ (↑ᵀ 𝓊̂)
```

The second implication is:

    Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ′ : T

```agda
Ⓡ-==↓ : ∀ {Γ′ Γ : Ctx} {T : Type} {t : Γ ⊢ T} {a : ⟦ T ⟧}
      → t Ⓡ a
        ---------------------
      → (Γ′≤Γ : Γ′ ≤ Γ)
      → Γ′≤Γ ≤⊢ t == ↓ᵀᵧ a
```

A consequence of the first implication is that
`Γ , x:T ⊢ x Ⓡ ↑ᵀ (𝓍̂ Γ)`, which we define now
as it will be the lemma we will need for proving the
second implication
```agda
xⓇ↑ᵀ𝓍̂ : ∀ {Γ : Ctx} {T : Type}
        -------------------------
      → ` `Z {Γ} {T} Ⓡ ↑ᵀ (𝓍̂ T Γ)
```

To prove the first implication, first we show that it always
holds for liftable neutral terms of type nat. This is simply
the given proof, so this case follows immediately.
```agda
==↑-Ⓡ {T = nat} pf Γ′≤Γ = pf Γ′≤Γ
```
Now, for liftable neutral terms of type S → T, we prove that
the relation holds for `↑ᵀ (𝓊̂ · ↓ˢ a)`

We prove the relation holds by using our induction
hypothesis, so that our new goal is to prove that

    Γ″ ⊢ 𝓊 s = (𝓊̂ · (↓ˢ a)) Γ″ : T

for any Γ″ that is an extension of Γ′ (which itself
extends Γ).

Note that `(𝓊̂ · (↓ˢ a)) Γ″` is equivalent to
`𝓊̂(Γ″) · (↓ˢ a)(Γ″)` (application of liftable neutrals is overloaded.

First, we deconstruct `𝓊̂ (Γ″)`,
using our given proof that it's definitionally
equal to `Γ″ ⊢ 𝓊 : S → T` to both discard the case
where `𝓊̂ (Γ″)` is undefined and simplify our goal
to proving that:

    Γ″ ⊢ 𝓊 · s = 𝓊″ · ↓ˢ a Γ″ : T (𝓊″ is 𝓊̂ lifted to the context Γ″)

We also use the other implication we will prove,
alongside the fact that `s Ⓡ a`, to have evidence
that `Γ″ ⊢ s : S` is definitionally equal to
`↓ˢ a Γ″`.

With these pieces in place, we can use equational reasoning for definitional
equality to prove the desired goal.
```agda
==↑-Ⓡ {T = _ ⇒ _} {𝓊} {𝓊̂} pf {Γ′} Γ′≤Γ {s} {a} sⓇa =
  ==↑-Ⓡ 𝓊·s==𝓊̂·↓ˢa
    where
      𝓊·s==𝓊̂·↓ˢa : ∀ {Γ″ : Ctx}
                 → (Γ″≤Γ′ : Γ″ ≤ Γ′)
                 → Γ″≤Γ′ ≤⊢ (Γ′≤Γ ≤⊢ 𝓊) · s ==↑ 𝓊̂ ·↑ (↓ᵀ a)
      𝓊·s==𝓊̂·↓ˢa  {Γ″} Γ″≤Γ′
        with 𝓊̂ Γ″           | pf (≤-trans Γ″≤Γ′ Γ′≤Γ)
      ... | inj₁ ⟨ 𝓊″ , _ ⟩ | 𝓊==𝓊″
        with Ⓡ-==↓ sⓇa Γ″≤Γ′
      ... | s==↓ᵀᵧa =
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
```

To prove the second implication, we proceed similarly
and first prove it for type nat. If the term is logically
related to zero, the implication holds immediately from
our given proof
```agda
Ⓡ-==↓ {T = nat} {a = zero} pf Γ′≤Γ with ↓ᵀ {nat} zero
... | _ = pf Γ′≤Γ
```
Otherwise, if the term is logically related to
a successor of a natural, our given proof
similarly leads to the implication, though for this case,
we additionally need a lemma showing
that if a term of type nat is definitionally
equal to an object a of type ℕ̂ (i.e. a natural
with embedded liftable neutrals), then it is
definitionally equal to the reification of
the object a. We can prove this by induction
on a.
```agda
Ⓡ-==↓ {Γ} {T = nat} {t} {suc a} pf Γ′≤Γ
  with pf Γ′≤Γ
... | ⟨ n , ⟨ t==sn , nⓇa ⟩ ⟩
  with nⓇa ≤-id
... | n==ℕ̂a rewrite [id]-identity {t = n} =
  begin
    Γ′≤Γ ≤⊢ t
  ==⟨ t==sn ⟩
    suc · n
  ==⟨ app-compatible refl (==ℕ̂→==↓ᵀ {a = a} n==ℕ̂a) ⟩
    suc · ↓ᵀᵧ a
  ∎
  where
    ==ℕ̂→==↓ᵀ : ∀ {Γ : Ctx} {n : Γ ⊢ nat} {a : ⟦ nat ⟧}
             → n ==ℕ̂ a
               ----------
             → n == ↓ᵀᵧ a
    ==ℕ̂→==↓ᵀ {a = zero} pf with ↓ᵀ {nat} zero
    ... | _ = pf
    ==ℕ̂→==↓ᵀ {Γ} {a = suc a} ⟨ n , ⟨ m==sn , n==a ⟩ ⟩
      with ↓ᵀ {nat} (suc a) | ==ℕ̂→==↓ᵀ {a = a} (n==a ≤-id)
    ... | _                 | pf
      rewrite [id]-identity {t = n} = trans m==sn (app-compatible refl pf)
    ==ℕ̂→==↓ᵀ {Γ} {t} {ne 𝓊̂} pf
      with 𝓊̂ Γ           | pf
    ... | inj₁ ⟨ 𝓊 , _ ⟩ | t==𝓊 = t==𝓊
```
Lastly for type nat, if the term is logically related to an
embedded liftable neutral, the implication also
holds immediately from our given proof
```agda
Ⓡ-==↓ {Γ′} {T = nat} {a = ne 𝓊̂} pf Γ′≤Γ
  with 𝓊̂ Γ′           | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩  | t==𝓊     = t==𝓊
```
For our inductive step, we prove the implication
for terms of type S → T. Our desired implication
is now:

    Γ′ ⊢ t = ↓ᵀ f Γ′ : T

which, by definition, expands to:

    Γ′ ⊢ t = λx. ↓ᵀ f a (Γ′ , x:S) : T (where a = ↑ᵀ 𝓍̂ˢ Γ′)

We prove this by η expanding t to `λx. t x` and
then using the compatibility rule for abstractions
of definitional equality to simplify our goal to
proving:

    Γ′ , x:S ⊢ t x = ↓ᵀ f a (Γ′, x:S)

Note that our inductive hypothesis is:

    t x Ⓡ f a implies t x = ↓ᵀ f a

This is exactly what we want to show, so now
all we need is to prove that `t x Ⓡ f a`.

Luckily, our given proof holds that t and f
are logically related, which is equivalent
to saying that if `x Ⓡ a` , then `t x Ⓡ f a`,
reducing what we have to prove only to
`x Ⓡ a`. We have been using "a" for simplicity,
but `a = ↑ᵀ 𝓍̂ˢ Γ′`, and we are mutually proving
that `x Ⓡ ↑ᵀ 𝓍̂`, so we use this lemma here
to finish our proof.
```agda
Ⓡ-==↓ {Γ′} {T = S ⇒ _} {t} {f} pf Γ′≤Γ =
  begin
    Γ′≤Γ ≤⊢ t
  ==⟨ η ⟩
    ƛ (S ↑⊢ Γ′≤Γ ≤⊢ t) · ` `Z
  ==⟨
    abs-compatible (
      begin
        (S ↑⊢ Γ′≤Γ ≤⊢ t) · ` `Z
      ==⟨ app-compatible subst-lemma refl ⟩
        (≤-ext Γ′≤Γ ≤⊢ t) [ subst-id ] · ` `Z
      ==⟨ Ⓡ-==↓ (pf (≤-ext Γ′≤Γ) xⓇa) ≤-id ⟩
        proj₁ (↓ᵀ (f a) (Γ′ , S))
      ∎
  )⟩
    proj₁ (↓ᵀ f Γ′)
  ∎
  where
    subst-lemma =
      ≡→== (≡-trans (incr-↑-≡ {Γ′≤Γ = Γ′≤Γ} {t = t}) (≡-sym [id]-identity))
    a = ↑ᵀ {S} (𝓍̂ S Γ′)
    xⓇa = xⓇ↑ᵀ𝓍̂ {Γ′} {S}
```

Using our first implication, we can quickly
prove that `Γ , x:T ⊢ x : T Ⓡ ↑ᵀ 𝓍̂`, as `Γ′ ⊢ x = 𝓍̂ Γ′ : T` for all
`Γ′ ≤ Γ , x:T`
```agda
xⓇ↑ᵀ𝓍̂ {_} {T} = ==↑-Ⓡ x==𝓍̂ where
  x==𝓍̂ : ∀ {Γ Γ′ : Ctx}
       → (Γ′≤Γ,T : Γ′ ≤ (Γ , T))
       → Γ′≤Γ,T ≤⊢ ` `Z ==↑ 𝓍̂ T Γ
  x==𝓍̂ {Γ} {Γ′} pf
    with Γ′ ≤? (Γ , T)
  ... | no ¬pf = ¬pf pf
  ... | yes pf′
    with 𝓍̂ T Γ | ≤-pf-irrelevance pf pf′
  ... | _      | refl
    with ren-≤ pf′
  ...| _ , _  = refl
```

Before moving forward, we also want to show that rec Ⓡ ⟦rec⟧.
This will be necessary for proving soundness, as we will need
proof that `Γ ⊢ rec = ↓ᵀ ⟦rec⟧ Γ : (T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T)`
(i.e. proof that our interpretation of rec is sound) to prove the
soundness of NbE
```agda
recⓇ⟦rec⟧ : ∀ {Γ : Ctx} {T : Type} → rec {Γ} {T} Ⓡ ⟦rec⟧
recⓇ⟦rec⟧ Γ′≤Γ {z} pf Γ″≤Γ′ pf′ Γ‴≤Γ″ {s = n} {zero} pf″
  with pf″ ≤-id
... | n==zero
  rewrite [id]-identity {t = n} =
  ==-Ⓡ-trans (app-compatible refl (sym n==zero))
    (==-Ⓡ-trans (sym β-rec-z) zⓇa)
    where
      Γ‴≤Γ′ = ≤-trans Γ‴≤Γ″ Γ″≤Γ′
      subst-lemma = ≡→== (≡-sym (weaken-compose Γ‴≤Γ″ Γ″≤Γ′ z))
      zⓇa = ==-Ⓡ-trans subst-lemma (Ⓡ-weaken {Γ′≤Γ = Γ‴≤Γ′} pf)

recⓇ⟦rec⟧ Γ′≤Γ {z} {az} pf Γ″≤Γ′ {s} {aₛ} pf′ Γ‴≤Γ″ {m} {suc aₙ} pf″
  with pf″ ≤-id
... | ⟨ n , ⟨ m==saₙ , nⓇaₙ ⟩ ⟩
  rewrite [id]-identity {t = m} =
    ==-Ⓡ-trans (app-compatible refl (sym m==saₙ))
      (==-Ⓡ-trans (sym β-rec-s) s·n·recⓇaₛ·aₙ·⟦rec⟧)
  where
    subst-lemma₁ = [id]-identity {t = Γ‴≤Γ″ ≤⊢ s}
    subst-lemma₂ = [id]-identity {t = n}

    rec·z·s·n = (Γ‴≤Γ″ ≤⊢ (Γ″≤Γ′ ≤⊢ rec · z) · s) · n

    ih : rec·z·s·n Ⓡ ⟦rec⟧ az aₛ aₙ
    ih = recⓇ⟦rec⟧ Γ′≤Γ pf Γ″≤Γ′ {s = s} pf′ Γ‴≤Γ″ {s = n} {aₙ} nⓇaₙ

    s·n·recⓇaₛ·aₙ·⟦rec⟧ : (Γ‴≤Γ″ ≤⊢ s) · n · rec·z·s·n Ⓡ aₛ aₙ (⟦rec⟧ az aₛ aₙ)
    s·n·recⓇaₛ·aₙ·⟦rec⟧ with pf′ Γ‴≤Γ″ {n} nⓇaₙ ≤-id ih
    ... | pf
      rewrite subst-lemma₁ | subst-lemma₂ = pf

recⓇ⟦rec⟧ {_} {T} Γ′≤Γ {z} {az} pf Γ″≤Γ′ {s} {aₛ} pf′ {Γ‴} Γ‴≤Γ″ {n} {ne 𝓊̂} pf″ =
  ==↑-Ⓡ rec==↑rec↑ where
    rec==↑rec↑ : ∀ {Γ⁗ : Ctx}
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
        Γ⁗,nat≤Γ⁗ = ≤-ext {T = nat} Γ⁗≤Γ″
        Γ⁗,nat,T≤Γ⁗ = ≤-ext {T = T} Γ⁗,nat≤Γ⁗
        Γ⁗,nat,T≤Γ⁗,nat = ≤-ext {T = T} (≤-id {Γ⁗ , nat})

        subst-lemma₁ = ≡-sym (incr-↑-≡ {Γ′≤Γ = Γ⁗≤Γ″} {S = nat} {t = s})
        subst-lemma₂ =
          ≡-sym (weaken-compose Γ⁗≤Γ‴ Γ‴≤Γ″ s)
        subst-lemma₃ = [id]-identity {t = T ↑⊢ nat ↑⊢ Γ⁗≤Γ‴ ≤⊢ Γ‴≤Γ″ ≤⊢ s}

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
          with Ⓡ-==↓ pf-Ⓡ ≤-id
        ... | pf-==↓
          rewrite subst-lemma₁ | subst-lemma₂ | subst-lemma₃ = pf-==↓

        subst-lemma₄ = ≡-sym (weaken-compose Γ⁗≤Γ‴ Γ‴≤Γ′ z)
        subst-lemma₅  = ≡-sym (weaken-compose Γ‴≤Γ″ Γ″≤Γ′ z)

        z==↓ᵀaz : Γ⁗≤Γ‴ ≤⊢ Γ‴≤Γ″ ≤⊢ Γ″≤Γ′ ≤⊢ z == proj₁ (↓ᵀ az Γ⁗)
        z==↓ᵀaz
          with Ⓡ-==↓ {Γ⁗} pf (≤-trans Γ⁗≤Γ‴ Γ‴≤Γ′)
        ... | pf
          rewrite subst-lemma₄ | subst-lemma₅ = pf
```

With that out of the way, having proved the lemma that
`Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ : T`, we have:
    Γ ⊢ t : T Ⓡ a ⇒ Γ ⊢ t = ↓ᵀ a Γ : T
which is what we wanted our logical relation to imply,
so that we can then show that `Γ ⊢ t : T Ⓡ a` for `a = ⟦t⟧ (↑ Γ)`

For this, we will establish that `Γ ⊢ t : T Ⓡ ⟦t⟧ (↑ Γ)`
using the fundamental lemma of logical relations. First,
we will need to extend logical relations to include
substitutions and environments. We again use ∥Ⓡ∥ for
the "parallel" in parallel substitutions, as Ⓡ is
already defined for terms and semantic objects
```agda
_∥Ⓡ∥_ : ∀ {Γ Δ : Ctx}
      → Sub Γ Δ
      → ⟦ Δ ⟧
      → Set
```

Similarly as for terms and values, a Kripe logical
relation between a parallel substitution and an
environment is defined inductively, though this time
by induction on the rules for parallel substitutions
instead of by induction on types

A substitution from the empty context is always
logically related to an empty environment
```agda
∅ ∥Ⓡ∥ tt = ⊤
```

An extension to a substition (σ , s / x) is logically
related to an environment (ρ , a) if σ is logically
related to ρ and s is logically related to a
```agda
(σ , s) ∥Ⓡ∥ ⟨ ρ , a ⟩ = σ ∥Ⓡ∥ ρ × s Ⓡ a

infix 4 _∥Ⓡ∥_
```

A consequence of how substitutions and their logical
relation with environments are defined is that we
have that a logical relation for a shifted substitution
holds if the logical relation holds for the original
substitution (as the shifted terms will be irrelevant)
```agda
∥Ⓡ∥-↑ : ∀ {Γ Δ : Ctx} {T : Type} {σᵣ : Ren Γ Δ} {ρ : ⟦ Δ ⟧}
      → subst-ren σᵣ ∥Ⓡ∥ ρ
      → subst-ren (_↑ᵣ {T = T} σᵣ) ∥Ⓡ∥ ρ
∥Ⓡ∥-↑ {σᵣ = ∅} pf = tt
∥Ⓡ∥-↑ {T = T} {σᵣ = _ , x} {⟨ _ , a ⟩} ⟨ pf , xⓇa ⟩ = ⟨ ∥Ⓡ∥-↑ pf , ↑⊢xⓇa ⟩
  where
    subst-lemma₁ = shift-var {S = T} {x = x} {σᵣ = ren-id}
    subst-lemma₂ = rename-id {x = x}

    Γ,T≤Γ = ≤-ext {T = T} ≤-id

    ↑⊢xⓇa : ` (`S x) Ⓡ a
    ↑⊢xⓇa
      with Ⓡ-weaken {Γ′≤Γ = Γ,T≤Γ} {t = ` x} xⓇa
    ... | pf
      rewrite subst-lemma₁ | subst-lemma₂ = pf
```

A generalization of this is, similarly as for logical relations
between terms and semantic objects, that if a logical relation
holds between a substitution and an environment, it holds for any
weakening of the substitution (as weakening is really a series
of shifts)
```agda
∥Ⓡ∥-weaken : ∀ {Γ′ Γ Δ : Ctx} {Γ′≤Γ : Γ′ ≤ Γ} {σ : Sub Γ Δ} {ρ : ⟦ Δ ⟧}
        → σ ∥Ⓡ∥ ρ
        → σ ∘ (weaken Γ′≤Γ) ∥Ⓡ∥ ρ
∥Ⓡ∥-weaken {σ = ∅} x = tt
∥Ⓡ∥-weaken {Γ′≤Γ = Γ′≤Γ} {σ , s} ⟨ σ∥Ⓡ∥ρ , sⓇa ⟩ =
  ⟨ ∥Ⓡ∥-weaken {Γ′≤Γ = Γ′≤Γ} σ∥Ⓡ∥ρ , Ⓡ-weaken {Γ′≤Γ = Γ′≤Γ} sⓇa ⟩
```

We are now ready to introduce the semantic typing judgement
`Γ ⊨ t : T`, which will be the what we will use to arrive
at `Γ ⊢ t : T Ⓡ ⟦ t ⟧ ↑Γ Γ`
```agda
_⊨_ : ∀ {T : Type} → (Γ : Ctx) → Γ ⊢ T → Set
_⊨_ {T} Γ t =
  ∀ {Δ : Ctx} {σ : Sub Δ Γ} {ρ : ⟦ Γ ⟧}
  → σ ∥Ⓡ∥ ρ
    -------
  → t [ σ ] Ⓡ ⟦⊢ t ⟧ ρ
```

By induction on the typing judgement `Γ ⊢ t : T`,
we prove the semantic typing judgement `Γ ⊨ t : T`,
this is called the fundamental lemma of logical
relations
```agda
fundamental-lemma : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
                  → Γ ⊨ t
fundamental-lemma {t = zero} σ∥Ⓡ∥ρ _ = refl
fundamental-lemma {t = suc} σ∥Ⓡ∥ρ Δ′≤Δ {s} {a} pf {Δ″} Δ″≤Δ′ =
  ⟨ Δ″≤Δ′ ≤⊢ s , ⟨ refl , s==a ⟩ ⟩
  where
    s==a : ∀ {Δ‴ : Ctx} → (Δ‴≤Δ″ : Δ‴ ≤ Δ″) → Δ‴≤Δ″ ≤⊢ Δ″≤Δ′ ≤⊢ s ==ℕ̂ a
    s==a Δ‴≤Δ″
      with pf (≤-trans Δ‴≤Δ″ Δ″≤Δ′)
    ... | pf
      rewrite weaken-compose Δ‴≤Δ″ Δ″≤Δ′ s = pf
fundamental-lemma {t = rec {T}} _ = recⓇ⟦rec⟧
fundamental-lemma {t = ` `Z} {σ = _ , _ } {⟨ _ , _ ⟩} ⟨ _ , xⓇa ⟩ = xⓇa
fundamental-lemma {t = ` (`S x)} {σ = _ , _} {⟨ _ , _ ⟩} ⟨ σ∥Ⓡ∥ρ , _ ⟩ =
  fundamental-lemma {t = ` x} σ∥Ⓡ∥ρ
fundamental-lemma {t = ƛ t} {σ = σ} {ρ} σ∥Ⓡ∥ρ Γ′≤Γ {s} {a} sⓇa =
  ==-Ⓡ-trans (sym β-ƛ) t[σ′][s/x]Ⓡ⟦t⟧⟨ρ,a⟩
  where
    subst-lemma₁ =
      subst-compose {τ = subst-id , s} {weaken Γ′≤Γ ↑ , ` `Z} {t [ σ ↑ , ` `Z ]}
    subst-lemma₂ =
     subst-compose {τ = ((weaken Γ′≤Γ ↑) ∘ (subst-id , s)) , s} {σ ↑ , ` `Z} {t}

    t[σ′] = t [ σ ↑ , ` `Z ] [ weaken Γ′≤Γ ↑ , ` `Z ]

    subst-lemma₃ = subst-compose-↑ {τ = subst-id} {weaken Γ′≤Γ} {s}
    subst-lemma₄ = subst-compose-↑ {τ = weaken Γ′≤Γ ∘ subst-id} {σ} {s}
    subst-lemma₅ = id-compose-identity {σ = weaken Γ′≤Γ}

    σ″ = ((σ ↑) ∘ (((weaken Γ′≤Γ ↑) ∘ (subst-id , s)) , s))

    σ″Ⓡρ : σ″  ∥Ⓡ∥ ρ
    σ″Ⓡρ rewrite subst-lemma₃ | subst-lemma₄ | subst-lemma₅ =
      ∥Ⓡ∥-weaken {Γ′≤Γ = Γ′≤Γ} σ∥Ⓡ∥ρ

    t[σ′][s/x]Ⓡ⟦t⟧⟨ρ,a⟩ : t[σ′] [ s /x] Ⓡ ⟦⊢ t ⟧ ⟨ ρ , a ⟩
    t[σ′][s/x]Ⓡ⟦t⟧⟨ρ,a⟩ rewrite subst-lemma₁ | subst-lemma₂ =
        fundamental-lemma {t = t} ⟨ σ″Ⓡρ , sⓇa ⟩
fundamental-lemma {t = r · s} {σ = σ} σ∥Ⓡ∥ρ
  with fundamental-lemma {t = r} σ∥Ⓡ∥ρ | fundamental-lemma {t = s} σ∥Ⓡ∥ρ
... | Γ⊨r                              | Γ⊨s
  with Γ⊨r ≤-id Γ⊨s
... | pf
  rewrite [id]-identity {t = r [ σ ]} = pf
```

For the identity substitution we have that `Γ ⊢ id : Γ Ⓡ ↑Γ` ,
which we prove by induction using our lemma that
`Γ,x:T ⊢ x : T Ⓡ ↑ᵀ (𝓍ᵀ Γ)` for every variable that we
are substituting for itself.

```agda
idⓇ↑Γ : ∀ {Γ : Ctx}
       → subst-id ∥Ⓡ∥ (↑ᶜᵗˣ Γ)
idⓇ↑Γ {∅} = tt
```
For our inductive step, our IH will give us that
`Γ ⊢ id : Γ Ⓡ ↑Γ Γ`, but we want proof that `Γ , x:T ⊢ id ↑ : Γ Ⓡ Γ`
(because the identity substitution is unwrapped to `(id ↑ , x / x)`
for the context` Γ , x:T`). Here, we use our lemma that if a
logical relation holds for a substitution and an environment
it holds for a shifting of the substition, allowing us to
transform our IH into our goal
```agda
idⓇ↑Γ {Γ , T} = ⟨ ∥Ⓡ∥-↑ {T = T} idⓇ↑Γ , xⓇ↑ᵀ𝓍̂ ⟩
```

With this fact, we arrive at the soundness of NbE. By the fundamental lemma,
given `Γ ⊢ id : Γ Ⓡ ↑Γ`, we have that `Γ ⊢ t [ id ] Ⓡ ⟦ t ⟧ ↑Γ` -- and
`t [ id ] ≡ t`.

Using the lemma that logical relation implies definitional
equality to the reified semantic object, we arrive at
`Γ ⊢ t = ↓ᵀᵧ ⟦ t ⟧ ↑Γ : T`, which is what we want to show
(i.e. `Γ ⊢ t = nf(t) : T`)
```agda
soundness : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
          → t == nf t
soundness {Γ} {T} {t}
  with fundamental-lemma {t = t} (idⓇ↑Γ {Γ})
... | tⓇ⟦t⟧↑Γ
  with Ⓡ-==↓ tⓇ⟦t⟧↑Γ ≤-id
... | t==↓ᵀᵧ⟦t⟧↑Γ
  rewrite [id]-identity {t = t [ subst-id ]}
        | [id]-identity {t = t}              = t==↓ᵀᵧ⟦t⟧↑Γ
```

#### References
