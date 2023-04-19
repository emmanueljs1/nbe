# System T

We start off by defining the language that we will
use to showcase normalization by evaluation, System T,
as is done in Section 2.1.
```agda
import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no)
open Eq using (_≡_; refl)

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
  ==→⟦≡⟧ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {ρ : ⟦ Γ ⟧}
         → t == t′
         → ⟦⊢ t ⟧ ρ ≡ ⟦⊢ t′ ⟧ ρ

completeness : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
             → t == t′
             → nf t ≡ nf t′
completeness {Γ} t==t′ rewrite ==→⟦≡⟧ {ρ = ↑ᶜᵗˣ Γ} t==t′ = refl
```
