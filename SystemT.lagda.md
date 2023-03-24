# System T

We start off by defining the language that we will
use to showcase normalization by evaluation, System T,
as is done in Section 2.1.
```agda
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary using (Dec; yes; no)
open Eq using (_≡_; refl)

module SystemT where
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
nat ≟Tp nat = yes refl
nat ≟Tp (S ⇒ T) = no λ()
(S₁ ⇒ T₁) ≟Tp nat = no λ()
(S₁ ⇒ T₁) ≟Tp (S₂ ⇒ T₂) with S₁ ≟Tp S₂ | T₁ ≟Tp T₂
... | no ¬pf   | no _      = no (λ where refl → ¬pf refl)
... | no ¬pf   | yes _     = no (λ where refl → ¬pf refl )
... | yes _    | no ¬pf    = no (λ where refl → ¬pf refl)
... | yes refl | yes refl  = yes refl
```

We continue with typing contexts, defined inductively
with the empty context, and extensions to contexts. As
we are using a de Brujin index representation, there
are no names when extending contexts (and really they
are just lists of types).
```agda
data Γ : Set where
  ∅ : Γ
  _,_ : Γ → Type → Γ

infixl 5 _,_

_≟Γ_ : ∀ (Γ′ Γ : Γ) → Dec (Γ′ ≡ Γ)
∅ ≟Γ ∅ = yes refl
∅ ≟Γ (_ , _) = no λ()
(_ , _) ≟Γ ∅ = no λ()
(Γ′ , S) ≟Γ (Γ , T) with Γ′ ≟Γ Γ | S ≟Tp T
... | no ¬pf   | no _     = no (λ where refl → ¬pf refl)
... | no ¬pf   | yes _    = no (λ where refl → ¬pf refl)
... | yes _    | no ¬pf   = no (λ where refl → ¬pf refl)
... | yes refl | yes refl = yes refl
```

We also define a relation detailing when one context is the
extension of another, this is introduced formally in a later
section but will be useful throughout. A context is an extension
of itself, and given that one context Γ′ extends another context
Γ, the first can be extended further and the relation will still hold.
```agda
data _≤_ : Γ → Γ → Set where
  ≤-id : ∀ {Γ : Γ} → Γ ≤ Γ

  ≤-ext : ∀ {Γ Γ′ : Γ} {T : Type}
        → Γ′ ≤ Γ
          ----------
        → Γ′ , T ≤ Γ

infix 4 _≤_

_≤?_ : ∀ (Γ′ Γ : Γ) → Dec (Γ′ ≤ Γ)
∅ ≤? ∅ = yes ≤-id
∅ ≤? (_ , _) = no λ()
(_ , _) ≤? ∅ = yes Γ≤∅ where
  Γ≤∅ : ∀ {Γ : Γ} → Γ ≤ ∅
  Γ≤∅ {∅} = ≤-id
  Γ≤∅ {Γ , _} with Γ≤∅ {Γ}
  ... | pf = ≤-ext pf
(Γ′ , T) ≤? Γ@(_ , _)
  with (Γ′ , T) ≟Γ Γ
... | yes refl = yes ≤-id
... | no Γ′≢Γ
  with Γ′ ≤? Γ
... | yes pf = yes (≤-ext pf)
... | no ¬pf =
  no λ where
    ≤-id → Γ′≢Γ refl
    (≤-ext pf) → ¬pf pf
```

We also introduce a lookup judgement for
contexts, which corresponds to a de Brujin
index.
```agda
data _∋_ : Γ → Type → Set where
  `Z : ∀ {Γ : Γ} {T : Type}
        ---------
      → Γ , T ∋ T

  `S_ : ∀ {Γ : Γ} {S T : Type}
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
data _⊢_ (Γ : Γ) : Type → Set where
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
ex0 : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T ⇒ T
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
in "parallel substitutions" for operations related
to this type).
```agda
data _⊩_ : Γ → Γ → Set where
  ∅ : ∀ {Γ} → Γ ⊩ ∅

  _,_ : ∀ {Γ Δ : Γ} {S : Type}
        → Γ ⊩ Δ
        → Γ ⊢ S
          ---------
        → Γ ⊩ Δ , S

infix 4 _⊩_
```

Before defining the application of a substitution
`Γ ⊢ t [ σ ] : `T, we introduce renaming.

Renaming is a specialized substitution where
we can only substitute variables with other
variables (i.e. a renaming `Γ ⊢ σᵨ : Δ` provides
a variable in Γ to replace for every variable in Δ).

It is necessary to first to define renamign substitutions
so that termination is guaranteed for our operations.

We will use the subscript 'ᵨ' to indicate a renaming substitution.
```agda
data _⊩ᵨ_ : Γ → Γ → Set where
  ∅ : ∀ {Γ : Γ} → Γ ⊩ᵨ ∅

  _,_ : ∀ {Γ Δ : Γ} {S : Type}
      → Γ ⊩ᵨ Δ
      → Γ ∋ S
        ------------
      → Γ ⊩ᵨ (Δ , S)

infix 4 _⊩ᵨ_
```

We can use a renaming substitution to convert
lookup judgements (i.e. rename variables). In fact, this
is the operation that we need to define separately to
guarantee termination of the application of a substitution.
```agda
rename : ∀ {Γ Δ : Γ} {T : Type}
       → Δ ∋ T
       → Γ ⊩ᵨ Δ
         ------
       → Γ ∋ T
rename `Z (σᵨ , x) = x
rename (`S x) (σᵨ , _) = rename x σᵨ
```

We define parallel substitutions and renaming substitutions
with the previous rules so that we can define a shifting operation
over them. Shifting a renaming substitution shifts all indices
in the renaming by one -- in other words, given a renaming between Γ
and Δ, we can create a renaming between Γ , T and Δ.

We will use this to extend a renaming under a binder.
```agda
_↑ᵨ : ∀ {Γ Δ : Γ} {T : Type}
    → Γ ⊩ᵨ Δ
      ------------
    → (Γ , T) ⊩ᵨ Δ
∅ ↑ᵨ = ∅
(σᵨ , x) ↑ᵨ = σᵨ ↑ᵨ , `S x

infix 6 _↑ᵨ
```

With this operation in place, we can define the application of a renaming
substitution to rebase a term from a context Δ to a context Γ, this is done
by using the renaming substitution to replace all variables used in the term by
their corresponding variables in Γ
```agda
_[_]ᵨ : ∀ {Γ Δ : Γ} {T : Type}
        → Δ ⊢ T
        → Γ ⊩ᵨ Δ
          ------
        → Γ ⊢ T
zero [ _ ]ᵨ = zero
suc [ _ ]ᵨ = suc
rec [ _ ]ᵨ = rec
(` `Z) [ _ , x ]ᵨ = ` x
(` (`S x)) [ σᵨ , _ ]ᵨ = (` x) [ σᵨ ]ᵨ
(ƛ t) [ σᵨ ]ᵨ = ƛ t [ σᵨ ↑ᵨ , `Z ]ᵨ
(r · s) [ σᵨ ]ᵨ = r [ σᵨ ]ᵨ · s [ σᵨ ]ᵨ

infix 8 _[_]ᵨ
```

We also define a few "primitive" renamings that will be convenient for general
substitutions:

- The identity and incrementing renaming, defined mutually. The identity
renaming leaves all variables unchanged, while the incrementing renaming
increments all variables (which are really just indices) by 1
```agda
idᵨ : ∀ {Γ : Γ} → Γ ⊩ᵨ Γ
incrᵨ : ∀ {Γ : Γ} {T : Type} → (Γ , T) ⊩ᵨ Γ

idᵨ {∅} = ∅
idᵨ {Γ , T} = incrᵨ , `Z

incrᵨ = idᵨ ↑ᵨ
```

- A renaming between a context Γ′ and Γ,
where Γ′ is an extension of Γ. This renaming
is really a series of shifts based on
how many extensions to Γ the context Γ′
contains
```agda
≤ᵨ : ∀ {Γ′ Γ : Γ} → Γ′ ≤ Γ → Γ′ ⊩ᵨ Γ
≤ᵨ ≤-id = idᵨ
≤ᵨ (≤-ext pf) = (≤ᵨ pf) ↑ᵨ
```

Since a renaming is really just a specialized substitution,
we can transform any renaming substitution into a parallel
substitution
```agda
substᵨ : ∀ {Γ Δ : Γ} → Γ ⊩ᵨ Δ → Γ ⊩ Δ
substᵨ ∅ = ∅
substᵨ (σᵨ , x) = substᵨ σᵨ , ` x
```

We can now use our renaming substitutions to build out
parallel substitutions and their operations, such that
their operations are guaranteed to terminate.

Similarly as for renaming substitutions, we define a shifting
operation for parallel substitutions, to be used for extending
a substitution under a binder.
```agda
_↑ : ∀ {Γ Δ : Γ} {T : Type}
      → Γ ⊩ Δ
        ---------
      → Γ , T ⊩ Δ
_↑ ∅ = ∅
_↑ (σ , s) = (σ ↑) , s [ incrᵨ ]ᵨ

infix 6 _↑
```

Now, we can define the application of a parallel substitution
`Γ ⊢ σ : Δ` to a term `Δ ⊢ t : T` (e.g. `t [ σ ]`)
```agda
_[_] : ∀ {Γ Δ : Γ} {T : Type}
     → Δ ⊢ T
     → Γ ⊩ Δ
       -----
     → Γ ⊢ T
zero [ σ ] = zero
suc [ σ ] = suc
rec [ σ ] = rec
(` `Z) [ _ , x ] = x
(` (`S x)) [ σ , _ ] = ` x [ σ ]
(ƛ t) [ σ ] = ƛ (t [ σ ↑ , ` `Z ])
(r · s) [ σ ] = r [ σ ] · s [ σ ]

infix 8 _[_]
```

Substitutions can also be composed, by applying
a substitution `Γ₁ ⊢ τ : Γ₂` to every term in a
substitution `Γ₂ ⊢ σ : Γ₃`
```agda
_∘_ : ∀ {Γ₁ Γ₂ Γ₃ : Γ} → Γ₂ ⊩ Γ₃ → Γ₁ ⊩ Γ₂ → Γ₁ ⊩ Γ₃
∅ ∘ _ = ∅
(σ , s) ∘ τ = (σ ∘ τ) , s [ τ ]
```

We will want a weakening substitution, that allows us
to weaken a well typed term in Γ to a context Γ′ that
extends Γ.

Really, this substitution is the renaming substitution
between extended contexts
```agda
weaken : ∀ {Γ′ Γ : Γ}
       → Γ′ ≤ Γ
         ------
       → Γ′ ⊩ Γ
weaken pf = substᵨ (≤ᵨ pf)
```

For convenience, we will also want some shorthand for
applying a weakening substitution to a term
```agda
_≤⊢_ : ∀ {Γ′ Γ : Γ} {T : Type} → Γ′ ≤ Γ → Γ ⊢ T → Γ′ ⊢ T
pf ≤⊢ t = t [ weaken pf ]

infixr 5 _≤⊢_
```

Additionally, we define an identity and incrementing
parallel substitution, which are simply the identity and
incrementing renaming substitutions
```agda
id : ∀ {Γ : Γ} → Γ ⊩ Γ
id = substᵨ idᵨ

incr : ∀ {Γ : Γ} {T : Type} → Γ , T ⊩ Γ
incr = substᵨ incrᵨ
```

The incrementing substitution will be used to establish
η-equivalence, we will also benfit from some shorthand for
its application to a term
```agda
_↑⊢_ : ∀ {Γ : Γ} {T : Type} → (S : Type) → Γ ⊢ T → Γ , S ⊢ T
_ ↑⊢ t = t [ incr ]

infixr 5 _↑⊢_
```

To establish β-equivalence, we define an operation for
substituting the first free variable in a term `Γ , x:S ⊢ t : T`
with a term `Γ ⊢ s : S` (i.e. `t [ s / x ]`), which is really
shorthand for `t [ id , s / x ]`
```agda
_[_/x] : ∀ {Γ : Γ} {S T : Type}
  → Γ , T ⊢ S
  → Γ ⊢ T
    ---------
  → Γ ⊢ S
s [ t /x] =  s [ id , t ]

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
data _==_ : ∀ {Γ : Γ} {T : Type} → Γ ⊢ T → Γ ⊢ T → Set where

  -- Computation rules
  β-rec-z : ∀ {Γ : Γ} {T : Type}
              {z : Γ ⊢ T}
              {s : Γ ⊢ nat ⇒ T ⇒ T}
              -----------------------
            → rec · z · s · zero == z

  β-rec-s : ∀ {Γ : Γ} {T : Type}
      {z : Γ ⊢ T}
      {s : Γ ⊢ nat ⇒ T ⇒ T}
      {n : Γ ⊢ nat}
      ----------------------------------------------------
    → rec · z · s · (suc · n) == s · n · (rec · z · s · n)

  β-ƛ : ∀ {Γ : Γ} {S T : Type}
          {t : Γ , S ⊢ T}
          {s : Γ ⊢ S}
          ----------------------
        → (ƛ t) · s == t [ s /x]

  -- Function extensionality, i.e. Γ ⊢ t = Γ ⊢ λx. t x : S ⇒ T
  η : ∀ {Γ : Γ} {S T : Type}
        {t : Γ ⊢ S ⇒ T}
        ----------------------
      → t == ƛ (S ↑⊢ t) · ` `Z

  -- Compatibility rules
  --
  -- Note that we do not need a rule for constants and variables as
  -- is given in the thesis as we are using an intrinsically typed
  -- representation, so refl catches all of these cases
  abs-compatible : ∀ {Γ : Γ} {S T : Type} {t t′ : Γ , S ⊢ T}
                   → t == t′
                     -----------
                   → ƛ t == ƛ t′

  app-compatible : ∀ {Γ : Γ} {S T : Type}
                     {r r′ : Γ ⊢ S ⇒ T} {s s′ : Γ ⊢ S}
                   → r == r′
                   → s == s′
                     ----------------
                   → r · s == r′ · s′

  -- Equivalence rules
  refl : ∀ {Γ : Γ} {T : Type} {t : Γ ⊢ T}
           ------
         → t == t

  sym : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T}
        → t == t′
          -------
        → t′ == t

  trans : ∀ {Γ : Γ} {T : Type} {t₁ t₂ t₃ : Γ ⊢ T}
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

  begin_ : ∀ {Γ : Γ} {T : Type} {t t′ : Γ ⊢ T}
    → t == t′
      ---------
    → t == t′
  begin pf = pf

  _==⟨_⟩_ : ∀ {Γ : Γ} {T : Type} {t₂ t₃ : Γ ⊢ T}
    → (t₁ : Γ ⊢ T)
    → t₁ == t₂
    → t₂ == t₃
      -----
    → t₁ == t₃
  t₁ ==⟨ t₁≡t₂ ⟩ t₂≡t₃  =  trans t₁≡t₂ t₂≡t₃

  _∎ : ∀ {Γ : Γ} {T : Type} → (t : Γ ⊢ T)
      -----
    → t == t
  t ∎  =  refl

open ==-Reasoning public
```

Now, we are ready to start defining the algorithm for Normalization by
Evaluation in [NbE](./NbE.lagda.md).
