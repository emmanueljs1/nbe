---
title: "Normalization by Evaluation"
author: Emmanuel Suárez Acevedo
---

### Background

This site is both an overview of normalization by evaluation and a formalization
in Agda of the algorithm for the simply typed lambda calculus, based largely on
its presentation in Chapter 2 of Andreas Abel's habilitation thesis,
"Normalization by Evaluation: Dependent Types and Impredicativity" [@nbe]. It
was compiled from a literate Agda file available
[here](https://github.com/emmanueljs1/nbe/blob/main/NbE.lagda.md) by following
the helpful advice in [this](https://jesper.sikanda.be/posts/literate-agda.html)
blog post by Jesper Cockx.

For clarity and readability, some parts of the source file are left out in this
rendering, and this will be called out when possible.

Some familiarity with Agda (e.g. such as having worked through the first part of
[Programming Languages Foundations in Agda](https://plfa.inf.ed.ac.uk/22.08/))
is assumed along with some knowledge of programming language foundations, though
the content is mostly self contained.

### Introduction

Consider the following term in the lambda calculus:

    λx. (λy. y) x

This term is not in its *normal form*, that is, it can still undergo some
reductions. In this case, we can apply a beta reduction under the first binder
and arrive at:

    `λx. x`

This new term is now the normal form of `λx. (λy. y) x`. What we've just done,
believe it or not, is normalization by evaluation!

Normalization by evaluation is a technique for deriving the normal form of a
term in an object language by *evaluating* the term in a meta language (a
language we are using to describe the object language). In this case, our
object language was the untyped lambda calculus, and our meta language was,
well, just plain English.

In essence, you can reduce a term by evaluating the parts that _can_ be
evaluated while leaving the parts that _can't_ untouched. That is the intuition
behind normalization by evaluation.

To actually formalize normalization by evaluation and prove its correctness in
Agda, the algorithm may seem to become less intuitive, but it will still be
based on this initial idea.

<!---
### Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open Eq using (refl; trans; sym; _≡_; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (_≡⟨⟩_; step-≡; begin_; _∎)

module NbE where

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```
--->

### STLC

The object language that will be used here to define normalization by evaluation
will be the simply-typed lambda calculus with `𝟙` ("unit") as a base type. It
has variables, functions, application, and a single value of type `𝟙`: `unit`.

```agda
data Type : Set where
  -- unit
  𝟙   : Type

  -- functions
  _⇒_ : ∀ (S T : Type) → Type
```

<!---
```agda
infixr 7 _⇒_
```
--->

A typing context (for which the metavariable `Γ` will be used) is either the
empty context `∅` or an extension to a context `Γ , x:S` mapping an object
language variable to a type (here, `Γ` is extended with the variable `x` mapped
to the type `S`).

The Agda definition does not actually mention variable names at all, and is
really just a list of types. This is because a de Brujin representation will be
used for variables, so instead of a name, a variable will be an index into the
list of types making up the context (i.e. a de Brujin index). For example, the
variable `x` in the context `Γ , x:S` would be represented simply as the zeroth
index.

```agda
data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx
```

<!---
```
infixl 5 _,_
```
--->

The de Brujin index representing a variable will not actually be a natural
number "index", but rather a lookup judgements into a context. These lookup
judgements are very similar to natural numbers (and their contructors have been
named suggestively based on this similarity: `𝑍` for zero and `𝑆` for
successor). Defining them this way instead of simply using Agda's natural
numbers will allow for an index into a context to always be well-defined (and
for variables to be intrinsically typed, as will be shown in a moment).

```agda
data _∋_ : Ctx → Type → Set where
  𝑍 : ∀ {Γ : Ctx} {T : Type}
        ---------
      → Γ , T ∋ T

  𝑆_ : ∀ {Γ : Ctx} {S T : Type}
      → Γ ∋ T
        ---------
      → Γ , S ∋ T
```

<!---
```
infix 4 _∋_
infix 9 𝑆_
```
--->

Using these, the context `∅, x:S, y:T` can be represented along with the
variable names `"x"` and `"y"` as is done in the following example.

```agda
module Example (S T : Type) where
  ∅,x:S,y:T = ∅ , S , T

  x : ∅,x:S,y:T ∋ S
  x = 𝑆 𝑍

  y : ∅,x:S,y:T ∋ T
  y = 𝑍
```

STLC terms will be embedded in Agda using an *intrinsically* typed
representation. Types are defined first, and terms are only every considered
with respect to their type.

Using this representation, terms that are not well-typed don't even have to be
considered, as they are impossible to represent. An STLC term `t` embedded in
Agda as an expression of type `Γ ⊢ T` is, by definition, a well-typed STLC
term of type `T` in the context `Γ` (written as `Γ ⊢ t : T`).

For clarity, when talking about terms their representation in the STLC will be
used over their intrinsically typed representation using de Brujin indices, and
all terms will be assumed to be well-typed. (e.g. the variable `# 𝑍` will be
referred to as `Γ , x:T ⊢ x : T`, or just `x`.)

```agda
data _⊢_ (Γ : Ctx) : Type → Set where
  -- unit term
  unit : Γ ⊢ 𝟙

  -- variable
  #_ : ∀ {S : Type}
     → Γ ∋ S
       -----
     → Γ ⊢ S

  -- abstraction
  ƛ_ : ∀ {S T : Type}
     → Γ , S ⊢ T
       ---------
     → Γ ⊢ S ⇒ T

  -- application
  _·_ : ∀ {S T : Type}
      → Γ ⊢ S ⇒ T
      → Γ ⊢ S
        ---------
      → Γ ⊢ T
```

<!---
```agda
infix 4 _⊢_
infix 5 ƛ_
infixl 7 _·_
infix 9 #_
```
--->

Here are some sample programs in STLC embedded here using these constructors:

```agda
-- Γ ⊢ λx. x : T → T
ex0 : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T ⇒ T
ex0 = ƛ # 𝑍

-- ∅ ⊢ (λx. x) unit : 𝟙
ex1 : ∅ ⊢ 𝟙
ex1 = ex0 · unit
```

With this embedding of the simply typed lambda calculus in Agda, an algorithm
for normalization by evaluation can actually be written. However, to prove
properties about the algorithm (e.g. that it is actually correct), a few more
language constructs are still needed. They are: context extension,
substitutions, and definitional equality. These will be defined before getting
into the details of the algorithm itself.

#### Context extension

When defining the algorithm for normalization by evaluation, it will be
necessary to determine whether or not a context is an extension of another. A
context `Γ′` extends another context `Γ` if every mapping in `Γ` is also in
`Γ′`.

Since contexts are really just lists in their Agda representation, `Γ′` will be
an extension of `Γ` if `Γ` is a "sublist" of `Γ′`. The relation for context
extension is defined inductively based somewhat on this idea: a context extends
itself, and given that a context `Γ′` extends another context `Γ`, an extension
of `Γ′` is still an extension of `Γ′`.

```agda
data _≤_ : Ctx → Ctx → Set where
  ≤-id : ∀ {Γ : Ctx} → Γ ≤ Γ

  ≤-ext : ∀ {Γ Γ′ : Ctx} {T : Type}
        → Γ′ ≤ Γ
          ----------
        → Γ′ , T ≤ Γ
```

<!---
```agda
infix 4 _≤_
```
--->

<!---

The relation is invertible: if `Γ′ ≤ Γ , T`, then `Γ′ ≤ Γ`.

```agda
invert-≤ : ∀ {Γ Γ′ : Ctx} {T : Type}
         → Γ′ ≤ Γ , T
           ----------
         → Γ′ ≤ Γ
invert-≤ ≤-id = ≤-ext ≤-id
invert-≤ (≤-ext x) = ≤-ext (invert-≤ x)
```
--->

The relation is antisymmetric, meaning that if `Γ′ ≤ Γ` and `Γ ≤ Γ′`, then
`Γ′` and `Γ` must be the same context. This proof is left out in the rendering,
though it is proven mutually with the fact that `Γ` is never an
extension of `Γ , x : T`.

```agda
≤-antisym : ∀ {Γ Γ′ : Ctx}
          → Γ ≤ Γ′
          → Γ′ ≤ Γ
            ------
          → Γ ≡ Γ′

Γ≰Γ,T : ∀ {Γ : Ctx} {T : Type} → ¬ (Γ ≤ Γ , T)
```

<!---
```agda
≤-ext-uniq-T : ∀ {Γ Γ′ : Ctx} {S T : Type}
           → Γ′ ≤ Γ , T
           → Γ′ ≤ Γ , S
             ----------
           → T ≡ S

≤-ext-uniq-T ≤-id ≤-id = refl
≤-ext-uniq-T ≤-id (≤-ext c) = ⊥-elim (Γ≰Γ,T c)
≤-ext-uniq-T (≤-ext c) ≤-id = ⊥-elim (Γ≰Γ,T c)
≤-ext-uniq-T (≤-ext p₁) (≤-ext p₂)
  rewrite ≤-ext-uniq-T p₁ p₂ = refl

≤-antisym ≤-id Γ′≤Γ = refl
≤-antisym (≤-ext Γ≤Γ′) ≤-id = refl
≤-antisym (≤-ext {T = T₁} p₁) (≤-ext {T = T₂} p₂)
  with invert-≤ p₁ | invert-≤ p₂
...  | ≤→         | ≤←
  with ≤-antisym ≤→ ≤←
...  | refl
  rewrite ≤-ext-uniq-T p₁ p₂     = refl

Γ≰Γ,T {Γ} {T} Γ≤Γ,T
  with ≤-ext {T = T} (≤-id {Γ})
...  | Γ,T≤Γ
  with ≤-antisym Γ≤Γ,T Γ,T≤Γ
...  | ()
```
--->

This relation is also transitive, a proof that follows by induction:

```agda
≤-trans : ∀ {Γ″ Γ′ Γ : Ctx}
         → Γ″ ≤ Γ′
         → Γ′ ≤ Γ
           -------
         → Γ″ ≤ Γ
≤-trans ≤-id ≤-id               = ≤-id
≤-trans ≤-id (≤-ext pf)         = ≤-ext pf
≤-trans (≤-ext pf) ≤-id         = ≤-ext pf
≤-trans (≤-ext pf₁) (≤-ext pf₂) = ≤-ext (≤-trans pf₁ (≤-ext pf₂))
```

Finally, this relation can be made decidable. Its decidability in requires that
equality between contexts (and by extension, type) also be decidable, though
these proofs are also left out in the rendering.

```agda
_≟Tp_ : ∀ (S T : Type) → Dec (S ≡ T)
```

<!---
```agda
𝟙         ≟Tp 𝟙                                    = yes refl
𝟙         ≟Tp (S ⇒ T)                              = no λ()
(S₁ ⇒ T₁) ≟Tp 𝟙                                    = no λ()
(S₁ ⇒ T₁) ≟Tp (S₂ ⇒ T₂) with S₁ ≟Tp S₂ | T₁ ≟Tp T₂
...                        | no ¬pf    | no _      = no λ{refl → ¬pf refl}
...                        | no ¬pf    | yes _     = no λ{refl → ¬pf refl}
...                        | yes _     | no ¬pf    = no λ{refl → ¬pf refl}
...                        | yes refl  | yes refl  = yes refl
```
--->

```agda
_≟Ctx_ : (Γ Γ′ : Ctx) → Dec (Γ ≡ Γ′)
```

<!---
```agda
∅       ≟Ctx ∅                                  = yes refl
∅       ≟Ctx (_ , _)                            = no λ()
(_ , _) ≟Ctx ∅                                  = no λ()
(Γ′ , S) ≟Ctx (Γ , T) with Γ′ ≟Ctx Γ | S ≟Tp T
...                      | no ¬pf    | no _     = no λ{refl → ¬pf refl}
...                      | no ¬pf    | yes _    = no λ{refl → ¬pf refl}
...                      | yes _     | no ¬pf   = no λ{refl → ¬pf refl}
...                      | yes refl  | yes refl = yes refl
```
--->

With these, the relation can be made decidable in Agda:

```agda
_≤?_ : ∀ (Γ′ Γ : Ctx) → Dec (Γ′ ≤ Γ)
∅        ≤? ∅          = yes ≤-id
∅        ≤? (_ , _)    = no λ()
(_ , _)  ≤? ∅          = yes Γ≤∅ where
  Γ≤∅ : ∀ {Γ : Ctx} → Γ ≤ ∅
  Γ≤∅ {∅}     = ≤-id
  Γ≤∅ {Γ , _} = ≤-ext Γ≤∅
(Γ′ , T) ≤? Γ@(_ , _)
  with (Γ′ , T) ≟Ctx Γ
...  | yes refl        = yes ≤-id
...  | no Γ′≢Γ
  with Γ′ ≤? Γ
...  | yes pf          = yes (≤-ext pf)
...  | no ¬pf          = no λ where
                           ≤-id       → Γ′≢Γ refl
                           (≤-ext pf) → ¬pf pf
```

### Substitution

A parallel substitution `Γ ⊢ σ : Δ` provides a term in `Γ` to substitute for
each variable in the context `Δ`. In other words, a substitution `σ` is a
function from variables in a context to terms in another context.

```agda
Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀ {T : Type} → Δ ∋ T → Γ ⊢ T
```

To actually use a substitution, an operation is needed to apply the substitution
to a term in the context being used by the substitution:


    Δ ⊢ σ : Γ      Δ ⊢ t : T
    ------------------------
         Γ ⊢ t [ σ ] : T

This operation would allow for transforming a term `t` that is well-typed in the
context `Δ` using a substitution `σ` that maps every variable in `Δ` to a term
that is well-typed in `Γ`.

Defining this operation is actually a little tricky in Agda, because the
typical definition of the application of a substitution `σ` is not obviously
terminating. To solve this problem, it is necessary to separately define a
smaller subset of substitution: renaming.

A renaming is a specialized substitution where the only terms that can be
substituted for variables are other variables (i.e. a renaming `Γ ⊢ ρ : Δ`
provides a variable in `Γ`, not a term in `Γ`, to replace for every variable
in `Δ`). 

```agda
Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {T : Type} → Δ ∋ T → Γ ∋ T
```

Any renaming can be transformed to the more general definition for
substitutions:

```agda
ren : ∀ {Γ Δ : Ctx} → Ren Γ Δ → Sub Γ Δ
ren ρ x = # ρ x
```

Two renamings that will be especially relevant are the identity renaming (which
substitutes variables for themselves) and the shifting renaming (which shifts
all variables by 1). To indicate that these are renamings specifically (as they
will also be defined for the more general definition of substitutions), the
subscript `ᵣ` is used.

```agda
idᵣ : ∀ {Γ : Ctx} → Ren Γ Γ
idᵣ x = x

↥ᵣ : ∀ {Γ : Ctx} {T : Type} → Ren (Γ , T) Γ
↥ᵣ x = 𝑆 x
```

Any two renamings can also be composed. For a renaming substitution, this is
really just function compostition. Agda's own symbol for function composition,
`∘`, is used for this reason (though again with the subscript `ᵣ`).

```agda
_∘ᵣ_ : ∀ {Γ Δ Σ : Ctx} → Ren Δ Γ → Ren Σ Δ → Ren Σ Γ
ρ ∘ᵣ ω = λ x → ω (ρ x)
```

<!---
```agda
infixr 9 _∘ᵣ_
```
--->

It is possible to define a renaming for a context `Γ′` using a context `Γ` that
it extends by composing many shifting renamings, ending finally at the identity
renaming.

```
ρ-≤ : ∀ {Γ′ Γ : Ctx} → Γ′ ≤ Γ → Ren Γ′ Γ
ρ-≤ ≤-id       = idᵣ
ρ-≤ (≤-ext pf) = ρ-≤ pf ∘ᵣ ↥ᵣ
```

The application of a renaming substituion `Γ ⊢ ρ : Δ` to a term `Δ ⊢ t : T`
rebases the term to the context `Γ`. This is done by "distributing" the
renaming substitution across all subterms of the term, renaming all variables
used in the term with their corresponding variable in `Γ`. When going under a
binder, the renaming substitution has to be "extended" (`ext`) to now use the
newly bound variable `𝑍`.

```agda
ext : ∀ {Γ Δ : Ctx} → Ren Γ Δ → ∀ {T : Type} → Ren (Γ , T) (Δ , T)
ext ρ 𝑍     = 𝑍
ext ρ (𝑆 x) = 𝑆 ρ x

_[_]ᵣ : ∀ {Γ Δ : Ctx} {T : Type}
      → Δ ⊢ T
      → Ren Γ Δ
        -------
      → Γ ⊢ T
unit [ _ ]ᵣ    = unit
# x [ ρ ]ᵣ     = # ρ x
(ƛ t) [ ρ ]ᵣ   = ƛ t [ ext ρ ]ᵣ
(r · s) [ ρ ]ᵣ = r [ ρ ]ᵣ · s [ ρ ]ᵣ
```

<!---
```agda
infix 8 _[_]ᵣ
```
--->

With the application of a renaming substitution, it is now possible to define
the application of any general substitution such that it is guaranteed to
terminate. Extending the terms in the substitution under a binder requires
applying a shifting substitution to every term in the binder. By defining
the application of renaming substitutions separately, extending a substitution
can be done such that the overall definition of the application `Γ ⊢ t [ σ ]: T`
of a substitution `Γ ⊢ σ : Δ` is guaranteed to be terminating. The definition is
very similar to the more specific application of a renaming substitution, except
variables are now being replcaed with entire terms.


```agda
exts : ∀ {Γ Δ : Ctx} → Sub Γ Δ → ∀ {T : Type} → Sub (Γ , T) (Δ , T)
exts σ 𝑍     = # 𝑍
exts σ (𝑆 x) = (σ x) [ ↥ᵣ ]ᵣ

_[_] : ∀ {Γ Δ : Ctx} {T : Type}
     → Δ ⊢ T
     → Sub Γ Δ
       -------
     → Γ ⊢ T
unit [ _ ]    = unit
# x [ σ ]     = σ x
(ƛ t) [ σ ]   = ƛ t [ exts σ ]
(r · s) [ σ ] = r [ σ ] · s [ σ ]
```

<!---
```
infix 8 _[_]
```
--->

The more general identity and shifting substitutions are defined exactly as they
were for renamings, except now the variable term is used. Parallel substitutions
can also be composed, by applying a substitution `Γ ⊢ τ : Δ` to every term in a
substitution `Δ ⊢ σ : Σ`.

```agda
id : ∀ {Γ : Ctx} → Sub Γ Γ
id x = # x

↥ : ∀ {Γ : Ctx} {T : Type} → Sub (Γ , T) Γ
↥ x = # 𝑆 x

_∘_ : ∀ {Γ Δ Σ : Ctx} → Sub Δ Γ → Sub Σ Δ → Sub Σ Γ
(σ ∘ τ) x = (σ x) [ τ ]
```

Any substitution `Γ ⊢ σ : Δ` can be extended with a well-typed term `Γ ⊢ s : S`
as well, which will be written as `Γ ⊢ σ ∷ s : Δ , x : S` (with `∷` used for
"cons").

```agda
_∷_ : ∀ {Γ Δ : Ctx} {S : Type} → Sub Γ Δ → Γ ⊢ S → Sub Γ (Δ , S)
(_ ∷ s) 𝑍     = s
(σ ∷ _) (𝑆 x) = σ x
```

<!---
```agda
infix 8 _∷_
infixr 9 _∘_
```
--->

Using the renaming substitution for context extension, any well-typed term in
`Γ` can be "weakened" to a well-typed term in a context `Γ′`. `≤⊢` will be used
as shorthand for the application of a weakening substitution (and in Agda, this
will look a lot like an extended judgement: `Γ′≤Γ ≤⊢ t`).

```agda
weaken : ∀ {Γ′ Γ : Ctx}
       → Γ′ ≤ Γ
         --------
       → Sub Γ′ Γ
weaken pf x = # ρ-≤ pf x

_≤⊢_ : ∀ {Γ′ Γ : Ctx} {T : Type} → Γ′ ≤ Γ → Γ ⊢ T → Γ′ ⊢ T
pf ≤⊢ t = t [ weaken pf ]
```

It will similarly be useful to introduce shorthand for the application of a
shifting substitution:

```agda
_↥⊢_ : ∀ {Γ : Ctx} {T : Type} → (S : Type) → Γ ⊢ T → Γ , S ⊢ T
_ ↥⊢ t = t [ ↥ ]
```

<!---
```
infixr 5 _↥⊢_
infixr 5 _≤⊢_
```
--->

To actually prove results about terms, a number of substitution lemmas will be
necessary. Their proofs are omitted, though they are directly inspired from the
[Substitution](https://plfa.github.io/20.07/Substitution/) chapter of PLFA. The
most import ones are `sub-sub` (substitutions can be composed) and
`[id]-identity` (the application of the identity substitution is an identity).

<!---
```agda
sub-head : ∀ {Γ Δ : Ctx} {T : Type} {t : Γ ⊢ T} {σ : Sub Γ Δ}
         → # 𝑍 [ σ ∷ t ] ≡ t
sub-head = refl

sub-tail : ∀ {Γ Δ : Ctx} {S T : Type} {s : Γ ⊢ S} {σ : Sub Γ Δ}
         → (↥ ∘ (σ ∷ s)) {T = T} ≡ σ
sub-tail = refl

sub-η : ∀ {Γ Δ : Ctx} {S T : Type} {σ : Sub Γ (Δ , S)}
      → (↥ ∘ σ ∷ (# 𝑍 [ σ ])) {T = T} ≡ σ
sub-η {Δ = Δ} {S} {T} {σ} = extensionality lemma where
  lemma : ∀ (x : Δ , S ∋ T) → (↥ ∘ σ ∷ (# 𝑍 [ σ ])) x ≡ σ x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

Z-shift : ∀ {Γ : Ctx} {S T : Type}
        → (↥ ∷ # 𝑍) ≡ id {Γ , S} {T}
Z-shift {Γ} {S} {T} = extensionality lemma where
  lemma : (x : Γ , S ∋ T) → (↥ ∷ # 𝑍) x ≡ id x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

sub-idL : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ} {T : Type}
        → id ∘ σ ≡ σ {T}
sub-idL = extensionality λ _ → refl

sub-dist : ∀ {Γ Δ Σ : Ctx} {S T : Type} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {s : Δ ⊢ S}
         → (σ ∷ s) ∘ τ ≡ (σ ∘ τ ∷ (s [ τ ])) {T}
sub-dist {Σ = Σ} {S} {T} {τ} {σ} {s} = extensionality lemma where
  lemma : ∀ (x : Σ , S ∋ T) → ((σ ∷ s) ∘ τ) x ≡ ((σ ∘ τ) ∷ (s [ τ ])) x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

sub-app : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ} {S T : Type} {r : Δ ⊢ S ⇒ T} {s : Δ ⊢ S}
        → (r · s) [ σ ] ≡ r [ σ ] · s [ σ ]
sub-app = refl

cong-ext : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ} {T : Type}
         → (∀ {S : Type} → ρ ≡ ρ′ {S})
         → ∀ {S : Type} → ext ρ {T} {S} ≡ ext ρ′
cong-ext {Δ = Δ} {ρ} {ρ′} {T} ρ≡ρ′ {S} = extensionality lemma where
  lemma : ∀ (x : Δ , T ∋ S) → ext ρ x ≡ ext ρ′ x
  lemma 𝑍                      = refl
  lemma (𝑆 x) rewrite ρ≡ρ′ {S} = refl

cong-rename : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ} {T : Type} {t : Δ ⊢ T}
            → (∀ {S : Type} → ρ ≡ ρ′ {S})
            → t [ ρ ]ᵣ ≡ t [ ρ′ ]ᵣ
cong-rename {t = unit} _                                                = refl
cong-rename {T = T} {# x} ρ≡ρ′ rewrite ρ≡ρ′ {T}                         = refl
cong-rename {ρ = ρ} {ρ′} {t = ƛ t} ρ≡ρ′
  rewrite cong-rename {ρ = ext ρ} {ρ′ = ext ρ′} {t = t} (cong-ext ρ≡ρ′) = refl
cong-rename {t = r · s} ρ≡ρ′
  rewrite cong-rename {t = r} ρ≡ρ′ | cong-rename {t = s} ρ≡ρ′           = refl

cong-exts : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ} {T : Type}
          → (∀ {S : Type} → σ ≡ σ′ {S})
          → (∀ {S : Type} → exts σ {T} {S} ≡ exts σ′)
cong-exts {Δ = Δ} {σ} {σ′} {T} σ≡σ′ {S} = extensionality lemma where
  lemma : ∀ (x : Δ , T ∋ S) → exts σ x ≡ exts σ′ x
  lemma 𝑍                      = refl
  lemma (𝑆 x) rewrite σ≡σ′ {S} = refl

cong-sub : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ} {T : Type} {t t′ : Δ ⊢ T}
         → (∀ {S : Type} → σ ≡ σ′ {S})
         → t ≡ t′
         → t [ σ ] ≡ t′ [ σ′ ]
cong-sub {t = unit} {unit} _ _                                          = refl
cong-sub {T = T} {t = # x} σ≡σ′ refl rewrite σ≡σ′ {T}                   = refl
cong-sub {σ = σ} {σ′} {t = ƛ t} σ≡σ′ refl
  rewrite cong-sub {σ = exts σ} {exts σ′} {t = t} (cong-exts σ≡σ′) refl = refl
cong-sub {σ = σ} {σ′} {t = r · s} σ≡σ′ refl
  rewrite cong-sub {σ = σ} {σ′} {t = r} σ≡σ′ refl
        | cong-sub {σ = σ} {σ′} {t = s} σ≡σ′ refl                       = refl

cong-cons : ∀ {Γ Δ : Ctx} {S : Type} {s s′ : Γ ⊢ S} {σ τ : Sub Γ Δ}
          → s ≡ s′
          → (∀ {T : Type} → σ {T} ≡ τ {T})
          → ∀ {T : Type} → σ ∷ s ≡ (τ ∷ s′) {T}
cong-cons {Δ = Δ} {S} {s} {s′} {σ} {τ} refl σ≡τ {T} = extensionality lemma where
  lemma : ∀ (x : Δ , S ∋ T) → (σ ∷ s) x ≡ (τ ∷ s′) x
  lemma 𝑍                     = refl
  lemma (𝑆 x) rewrite σ≡τ {T} = refl

cong-seq : ∀ {Γ Δ Σ : Ctx} {τ τ′ : Sub Γ Δ} {σ σ′ : Sub Δ Σ}
         → (∀ {T : Type} → σ {T} ≡ σ′)
         → (∀ {T : Type} → τ {T} ≡ τ′)
         → (∀ {T : Type} → (σ ∘ τ) {T} ≡ σ′ ∘ τ′)
cong-seq {Σ = Σ} {τ} {τ′} {σ} {σ′} σ≡σ′ τ≡τ′ {T} = extensionality lemma where
  lemma : ∀ (x : Σ ∋ T) → (σ ∘ τ) x ≡ (σ′ ∘ τ′) x
  lemma x rewrite σ≡σ′ {T} | cong-sub {t = σ′ x} τ≡τ′ refl = refl

ren-ext : ∀ {Γ Δ : Ctx} {S T : Type} {ρ : Ren Γ Δ}
        → ren (ext ρ) ≡ exts (ren ρ) {S} {T}
ren-ext {Δ = Δ} {S} {T} {ρ} = extensionality lemma where
  lemma : ∀ (x : Δ , S ∋ T) → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

rename-subst-ren : ∀ {Γ Δ : Ctx} {T : Type} {ρ : Ren Γ Δ} {t : Δ ⊢ T}
                 → t [ ρ ]ᵣ ≡ t [ ren ρ ]
rename-subst-ren {t = unit}                                           = refl
rename-subst-ren {t = # x}                                            = refl
rename-subst-ren {ρ = ρ} {ƛ t}
  rewrite rename-subst-ren {ρ = ext ρ} {t}
        | cong-sub {t = t} (ren-ext {ρ = ρ}) refl                     = refl
rename-subst-ren {ρ = ρ} {r · s}
  rewrite rename-subst-ren {ρ = ρ} {r} | rename-subst-ren {ρ = ρ} {s} = refl

ren-shift : ∀ {Γ : Ctx} {S T : Type}
          → ren ↥ᵣ ≡ ↥ {Γ} {S} {T}
ren-shift {Γ} {S} {T} = extensionality lemma where
  lemma : ∀ (x : Γ ∋ T) → ren ↥ᵣ x ≡ ↥ x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

rename-shift : ∀ {Γ : Ctx} {S T : Type} {s : Γ ⊢ S}
             → s [ ↥ᵣ {T = T} ]ᵣ ≡ s [ ↥ ]
rename-shift {Γ} {S} {T} {s}
  rewrite rename-subst-ren {ρ = ↥ᵣ {T = T}} {s}
        | ren-shift {Γ} {T} {S}                = refl

exts-cons-shift : ∀ {Γ Δ : Ctx} {S T : Type} {σ : Sub Γ Δ}
                → exts σ {S} {T} ≡ (σ ∘ ↥) ∷ # 𝑍
exts-cons-shift {Δ = Δ} {S} {T} {σ} = extensionality lemma where
  lemma : ∀ (x : Δ , S ∋ T) → exts σ x ≡ ((σ ∘ ↥) ∷ # 𝑍) x
  lemma 𝑍     = refl
  lemma (𝑆 x) = rename-subst-ren

ext-cons-Z-shift : ∀ {Γ Δ : Ctx} {ρ : Ren Γ Δ} {S T : Type}
                 → ren (ext ρ {T = S}) ≡ ((ren ρ ∘ ↥) ∷ # 𝑍) {T}
ext-cons-Z-shift {ρ = ρ} {S} {T}
  rewrite ren-ext {S = S} {T} {ρ}
        | exts-cons-shift {S = S} {T} {ren ρ} = refl

sub-abs : ∀ {Γ Δ : Ctx} {S T : Type} {σ : Sub Γ Δ} {t : Δ , S ⊢ T}
        → (ƛ t) [ σ ] ≡ ƛ t [ (σ ∘ ↥) ∷ # 𝑍 ]
sub-abs {σ = σ} {t}
  rewrite cong-sub {t = t} (exts-cons-shift {σ = σ}) refl = refl

exts-ids : ∀ {Γ : Ctx} {S T : Type}
         → exts id ≡ id {Γ , S} {T}
exts-ids {Γ} {S} {T} = extensionality lemma where
  lemma : ∀ (x : Γ , S ∋ T) → exts id x ≡ id x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl
```
--->

```agda
[id]-identity : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
              → t [ id ] ≡ t
```

<!---
```agda
[id]-identity {t = unit}                                = refl
[id]-identity {t = # x}                                 = refl
[id]-identity {T = S ⇒ T} {ƛ t}
  rewrite cong-sub {t = t} exts-ids refl
        | [id]-identity {t = t}                         = refl
[id]-identity {t = r · s}
  rewrite [id]-identity {t = r} | [id]-identity {t = s} = refl

sub-idR : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ} {T : Type}
        → (σ ∘ id) ≡ σ {T}
sub-idR = extensionality (λ _ → [id]-identity)

compose-ext : ∀ {Γ Δ Σ : Ctx} {ρ : Ren Δ Σ} {ω : Ren Γ Δ} {S T : Type}
            → (ext ρ) ∘ᵣ (ext ω) ≡ ext (ρ ∘ᵣ ω) {S} {T}
compose-ext {Σ = Σ} {ρ} {ω} {S} {T} = extensionality lemma where
  lemma : ∀ (x : Σ , S ∋ T) → ((ext ρ) ∘ᵣ (ext ω)) x ≡ ext (ρ ∘ᵣ ω) x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

compose-rename : ∀ {Γ Δ Σ : Ctx} {T : Type} {t : Σ ⊢ T} {ω : Ren Γ Δ}
                   {ρ : Ren Δ Σ}
               → t [ ρ ]ᵣ [ ω ]ᵣ ≡ t [ ρ ∘ᵣ ω ]ᵣ
compose-rename {t = unit}                               = refl
compose-rename {t = # x}                                = refl
compose-rename {T = S ⇒ T} {ƛ t} {ω} {ρ}
  rewrite compose-rename {t = t} {ext ω} {ext ρ}
        | cong-rename {t = t} (compose-ext {ρ = ρ} {ω}) = refl
compose-rename {t = r · s} {ω} {ρ}
  rewrite compose-rename {t = r} {ω} {ρ}
        | compose-rename {t = s} {ω} {ρ}                = refl

commute-subst-rename : ∀ {Γ Δ Σ Φ : Ctx} {T : Type} {t : Σ ⊢ T}
                         {σ : Sub Γ Δ} {ρ : Ren Δ Σ}
                         {ρ′ : Ren Γ Φ } {σ′ : Sub Φ Σ}
                     → (∀ {S : Type} {x : Σ ∋ S} → σ (ρ x) ≡ σ′ x [ ρ′ ]ᵣ)
                     → t [ ρ ]ᵣ [ σ ] ≡ t [ σ′ ] [ ρ′ ]ᵣ
commute-subst-rename {t = unit} pf = refl
commute-subst-rename {t = # x} pf = pf
commute-subst-rename {Σ = Σ} {T = S ⇒ T} {ƛ t} {σ} {ρ} {ρ′} {σ′} pf =
  cong ƛ_ (commute-subst-rename {t = t} (λ {_} {x} → H x))
  where
    H : ∀ {U : Type} (x : Σ , S ∋ U) → exts σ (ext ρ x) ≡ exts σ′ x [ ext ρ′ ]ᵣ
    H 𝑍 = refl
    H (𝑆 x) rewrite pf {x = x}
                  | compose-rename {t = σ′ x} {↥ᵣ {T = S}} {ρ′}
                  | compose-rename {t = σ′ x} {ext ρ′ {S}} {↥ᵣ} = refl
commute-subst-rename {t = r · s} {σ} {ρ} {ρ′} {σ′} pf
  rewrite commute-subst-rename {t = r} {σ} {ρ} {ρ′} {σ′} pf
        | commute-subst-rename {t = s} {σ} {ρ} {ρ′} {σ′} pf = refl

sub-𝑆-shift : ∀ {Γ Δ : Ctx} {S T : Type} {σ : Sub Γ (Δ , S)} {x : Δ ∋ T}
            → σ (𝑆_ {T = T} x) ≡ (↥ ∘ σ) x
sub-𝑆-shift = refl

exts-seq : ∀ {Γ Δ Σ : Ctx} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {S : Type}
         → ∀ {T : Type} → (exts σ ∘ exts τ) ≡ exts (σ ∘ τ) {S} {T}
exts-seq {Σ = Σ} {τ} {σ} {S} {T} = extensionality lemma where
  lemma : ∀ (x : Σ , S ∋ T) → (exts σ ∘ exts τ) x ≡ exts (σ ∘ τ) x
  lemma 𝑍  = refl
  lemma (𝑆 x) rewrite sub-𝑆-shift {S = S} {σ = exts σ ∘ exts τ} {x} =
    commute-subst-rename {t = σ x} refl
```
--->

```agda
sub-sub : ∀ {Γ Δ Σ : Ctx} {T : Type} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {t : Σ ⊢ T}
        → t [ σ ] [ τ ] ≡ t [ σ ∘ τ ]
```

<!---
```agda
sub-sub {t = unit} = refl
sub-sub {t = # x} = refl
sub-sub {τ = τ} {σ} {ƛ t} =
  begin
    (ƛ t) [ σ ] [ τ ]
  ≡⟨⟩
    ƛ t [ exts σ ] [ exts τ ]
  ≡⟨ cong ƛ_ (sub-sub {τ = exts τ} {exts σ} {t}) ⟩
    ƛ t [ exts σ ∘ exts τ ]
  ≡⟨ cong ƛ_ (cong-sub {t = t} exts-seq refl) ⟩
    ƛ t [ exts (σ ∘ τ) ]
  ∎
sub-sub {τ = τ} {σ} {r · s}
  rewrite sub-sub {τ = τ} {σ} {r} | sub-sub {τ = τ} {σ} {s} = refl

sub-assoc : ∀ {Γ Δ Σ Φ : Ctx} {σ : Sub Δ Γ} {τ : Sub Σ Δ} {θ : Sub Φ Σ}
          → ∀ {T : Type} → (σ ∘ τ) ∘ θ ≡ (σ ∘ τ ∘ θ) {T}
sub-assoc {Γ} {σ = σ} {τ} {θ} {T} = extensionality lemma where
  lemma : ∀ (x : Γ ∋ T) → ((σ ∘ τ) ∘ θ) x ≡ (σ ∘ τ ∘ θ) x
  lemma x rewrite sub-sub {τ = θ} {τ} {t = σ x} = refl

subst-zero-exts-cons : ∀ {Γ Δ : Ctx} {S T : Type} {σ : Sub Γ Δ} {s : Γ ⊢ S}
                     → exts σ ∘ (id ∷ s) ≡ (σ ∷ s) {T}
subst-zero-exts-cons {S = S} {T} {σ} {s} =
  begin
    exts σ ∘ (id ∷ s)
  ≡⟨ cong-seq exts-cons-shift refl ⟩
    ((σ ∘ ↥) ∷ # 𝑍) ∘ (id ∷ s)
  ≡⟨ sub-dist ⟩
    ((σ ∘ ↥) ∘ (id ∷ s)) ∷ s
  ≡⟨ cong-cons refl (sub-assoc {σ = σ}) ⟩
    (σ ∘ ↥ ∘ (id ∷ s)) ∷ s
  ≡⟨ cong-cons refl (cong-seq {σ = σ} refl (sub-tail {s = s} {σ = id})) ⟩
    (σ ∘ id) ∷ s
  ≡⟨ cong-cons refl (sub-idR {σ = σ}) ⟩
    σ ∷ s
  ∎
```
--->

### Definitional Equality

There is still one language construct left to define ─ equality. To explain why
an embedding of equality in Agda is needed, we can begin discussing
normalization by evaluation in more detail.

Normalization by evaluation is an algorithm for normalization, the process of
transforming a term into its normal form. The normal form of a term is *unique*,
being the term with all possible reductions (i.e. "computations") applied to it.
For any normalization algorithm `nf` such that `nf(t)` is the normal form of a
term `Γ ⊢ t : T`, we would expect the following properties to hold.

  - `Γ ⊢ nf(t) : T` (well-typedness of normal form)

    A normalization algorithm should still produce a term that is well-typed
    under the context `Γ` (and with the same type)

  - `nf(nf(t)) = nf(t)` (idempotency)

    This property refers to the "normalization" part of the algorithm ─ it
    should actually produce a term that has been fully normalized, i.e. it
    cannot undergo any more normalization.

  - `⟦ nf(t) ⟧ = ⟦ t ⟧` (preservation of meaning)

      We want an algorithm for normalization by evaluation to ensure that the
      normal form of a term that is obtained is _semantically equal_ to the
      original term. Put simply, this means that the two terms must have the
      same meaning.

      The `⟦ t ⟧` notation here indicates the *denotation* of `t`, which is
      equivalent to its meaning (in some meta-language).

Equality of functions is undecidable, so the last property is especially tricky
to prove for any algorithm. Instead, we will want to use βη-equivalence, or
_definitional equality_. In STLC, we have that two terms are definitionally
equal if and only if they have the same meaning. By proving that
`Γ ⊢ nf(t) = t : T`, that the normal form of a term is definitionally equal to
the original term, we will be proving that the normal form of a term preserves
the meaning of the original term.

To actually define βη-equivalence, we need to first define operations for
β-reductions and η-expansions.

A β-reduction will be the application of a substitution `t [ s / x ]` that
substitutes the term `s` for the variable `x` in the term `t`. In Agda, this
substitution will be an extension to the identity substitution with the term
`s` used for the first term in the substitution. For convenience, we will use
`t [ s ]₀` (as we are replacing the zeroth term in the identity substitution).

```agda
_[_]₀ : ∀ {Γ : Ctx} {S T : Type}
  → Γ , S ⊢ T
  → Γ ⊢ S
    ---------
  → Γ ⊢ T
_[_]₀ {Γ} {S} t s = t [ id ∷ s ]
```

<!---
```
infix 8 _[_]₀
```
--->

η-expansion for a functional term `Γ ⊢ t : S → T` will be an abstraction
`Γ ⊢ λx . t x : S → T` containing the application of a variable `Γ , x:S ⊢ x :
S` to the term `t`. The term `t` needs to have a shifting substitution applied
to it as we are using an intrinsically-typed representation (in changing the
context from `Γ` to `Γ , x:S`, the expression `t` itself also changes).

```agda
η-expand : ∀ {Γ : Ctx} {S T : Type}
         → Γ ⊢ S ⇒ T
         → Γ ⊢ S ⇒ T
η-expand {S = S} t = ƛ (S ↥⊢ t) · # 𝑍
```

With these defined, we can actually introduce definitional equality in Agda.
We use `t == t′` in Agda instead of `Γ ⊢ t = t′ : T`, though we will refer to
two terms that are definitionally equal with the latter.

```agda
data _==_ : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → Γ ⊢ T → Set where
  -- computation rule: beta reduction
  β : ∀ {Γ : Ctx} {S T : Type}
          {t : Γ , S ⊢ T}
          {s : Γ ⊢ S}
          ----------------------
        → (ƛ t) · s == t [ s ]₀

  -- η-expansion / function extensionality, i.e. Γ ⊢ t = Γ ⊢ λx. t x : S ⇒ T
  η : ∀ {Γ : Ctx} {S T : Type}
        {t : Γ ⊢ S ⇒ T}
        ----------------------
      → t == η-expand t

  -- compatibility rules
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

  -- equivalence rules
  refl⁼⁼ : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
           ------
         → t == t

  sym⁼⁼ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
        → t == t′
          -------
        → t′ == t

  trans⁼⁼ : ∀ {Γ : Ctx} {T : Type} {t₁ t₂ t₃ : Γ ⊢ T}
          → t₁ == t₂
          → t₂ == t₃
            --------
          → t₁ == t₃
```

<!---
```
infix 3 _==_
```
--->

For the readability of some of the proofs that will follow, it will be helpful
to have equational reasoning defined with respect to definitional equality. Its
definition is almost identical to Agda's own equational reasoning for
propositional equality, so it is left out in the rendering.

<!---
```agda
module ==-Reasoning where

  infix  1 begin==_
  infixr 2 _==⟨_⟩_
  infix  3 _==∎

  begin==_ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
           → t == t′
             -------
           → t == t′
  begin== pf = pf

  _==⟨_⟩_ : ∀ {Γ : Ctx} {T : Type} {t₂ t₃ : Γ ⊢ T}
          → (t₁ : Γ ⊢ T)
          → t₁ == t₂
          → t₂ == t₃
            --------
          → t₁ == t₃
  t₁ ==⟨ t₁≡t₂ ⟩ t₂≡t₃  =  trans⁼⁼ t₁≡t₂ t₂≡t₃

  _==∎ : ∀ {Γ : Ctx} {T : Type} → (t : Γ ⊢ T)
         ------
       → t == t
  t ==∎  =  refl⁼⁼
```
--->

<!---
```agda
open ==-Reasoning public
```
--->

Propositional equality implies definitional equality, a fact that will be
helpful to include here for later use.

```agda
≡→== : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
     → t ≡ t′
       -------
     → t == t′
≡→== pf rewrite pf = refl⁼⁼
```

### Evaluation

The evaluation, or interpretation, `⟦ t ⟧` of a well-typed term `Γ ⊢ t : T`
assigns a meaning to `t` by equating it to a semantic object in our meta
language, using an interpretation of the context `Γ` (an _environment_) under
which the term `t` is well-typed.

For types, we can interpret `𝟙` as Agda's own unit type, `⊤`, and functions as
Agda functions, with their meaning defined inductively.

    ⟦ 𝟙 ⟧ = ⊤
    ⟦ S ⇒ T ⟧ = ⟦ S ⟧ → ⟦ T ⟧

An empty context is interpreted as the unit type (an "empty" environment), and
an extension to a context is defined inductively, with the extension itself
being the interpretation of the type the context is extended with.

    ⟦ ∅ ⟧ = ⊤
    ⟦ Γ , S ⟧ = ⟦ Γ ⟧ × ⟦ S ⟧

From now on, we will use the metavariable `ε` to represent environments.

The interpretation of a variable expects an environment, and is essentially a
lookup into the environment for the variable's value:

    ⟦ Γ ∋ x:T ⟧ (ε ∈ ⟦ Γ ⟧) ∈ ⟦ T ⟧
    ⟦ Γ , T ∋ x:T ⟧ (ε , a) = a
    ⟦ Γ , y:S ∋ x:T ⟧ (ε , _) = ⟦ Γ ∋ x:T ⟧ ε

The interpretation of a typed term expects an environment as well.

    ⟦ Γ ⊢ t : T ⟧ (ε ∈ ⟦Γ⟧) ∈ ⟦ T ⟧
    ⟦ Γ ⊢ unit : 𝟙 ⟧ ε       = tt
    ⟦ Γ ⊢ x : T ⟧ ε          = ⟦ Γ ∋ x:T ⟧ ε
    ⟦ Γ ⊢ λx . t : S ⇒ T ⟧ ε = λ a → ⟦ Γ , x:S ⊢ t : T ⟧ (ε , a)
    ⟦ Γ ⊢ r s : T ⟧ ε        = (⟦ Γ ⊢ r : S ⇒ T ⟧ ε) (⟦ Γ ⊢ s : S ⟧ ε)

Before moving forward, we introduce the record we will use to represent
interpretations of types and contexts. For now, we will only include the
interpretation of a context as an environment, as our interpretation of types
will change subtly to better fit our algorithm for normalization by evaluation ─
this is also why we have only discussed evaluation at a high level.

```agda
record Interpretation (D : Set) : Set₁ where
  field
    ⟦_⟧ : D → Set

open Interpretation ⦃...⦄ public

instance
    ⟦Γ⟧ : ⦃ _ : Interpretation Type ⦄ → Interpretation Ctx
    Interpretation.⟦ ⟦Γ⟧ ⟧ ∅ = ⊤
    Interpretation.⟦ ⟦Γ⟧ ⟧ (Γ , T) = ⟦ Γ ⟧ × ⟦ T ⟧
```

### Normalization by Evaluation

The key idea behind normalization by evaluation is that we have inherently
performed some normalization of the term `t` in its evaluation -- if `t` was an
application `r s`, we are actually performing that application and reducing the
term. Normalization by evaluation as an algorithm takes advantage of this fact.

An issue with this view is that evaluation is not actually giving us the normal
form of a term, but rather its meaning as a semantic object in our meta
language. An algorithm for normalization by evaluation would need a way to to
convert a semantic object in our meta language back into a term in the object
language.

One way to achieve this is to evaluate (i.e. normalize) the parts of the
expression that actually _can_ be evaluated (such as function application),
while leaving the parts that cannot intact. Under this view, normalization by evaluation becomes the evaluation of an expression with unknowns (i.e. variables)
to another, possibly simplified, expression with unknowns.

To get this behavior, we make a subtle change to the "meaning" of a term in the meta language -- instead of terms of type `𝟙` mapping to Agda's unit type, they
will now evaluate to terms in their normal form.

This is a subtle distinction with a significant impact on the algorithm we will
define. We can now easily convert back to the object language, because
technically we never left it to begin with.

More concretely, we will be mapping a term `Γ ⊢ t : T` to an Agda data type used
to represent a term in its normal form. Terms in their normal form (normal
terms) will be defined mutually with terms that are blocked on evaluation
because they are unknown (neutral terms).

```agda
data Nf : (T : Type) → (Γ : Ctx) → Γ ⊢ T → Set -- Normal terms
data Ne (T : Type) (Γ : Ctx) : Γ ⊢ T → Set     -- Neutral terms
```

Now, the interpretation of a term of type `𝟙` can be changed to what we would
want it to be to define a suitable algorithm for normalization by evaluation:

    ⟦ 𝟙 ⟧ = Nf 𝟙

Note that our definition of normal terms is indexed both by a type and a
context, yet here the interpretation of a type is only indexed by the type
itself. We will get to this later, but it is for this reason that we have again
not written an implementation out in Agda yet. For now, we can give an initial
sketch of the algorithm, using a _reflection_ function `↑ᵀ` that maps neutral
terms of type `T` to semantic objects in `⟦ T ⟧`, and a _reification_ function
`↓ᵀ` for mapping a semantic object in `⟦ T ⟧` to normal forms of type `T`:

Putting all of these pieces together, we can present (in pseudo-code) what an
algorithm for normalization by evaluation would do.

    ⟦ 𝟙 ⟧ = Nf 𝟙
    ⟦ S → T ⟧ = ⟦ S ⟧ → ⟦ T ⟧

    ↑ᵀ ∈ Ne T → ⟦ T ⟧
    ↑ᵘⁿⁱᵗ 𝓊 = 𝓊
    ↑ˢ  ⃕ ᵗ 𝓊 (a ∈ ⟦ S ⟧) = ↑ᵀ (𝓊 𝓋) , 𝓋 = ↓ˢ a
    
    ↓ᵀ ∈ ⟦ T ⟧ → Nf T
    ↓ᵘⁿⁱᵗ 𝓋 = 𝓋
    ↓ˢ  ⃕ ᵗ f = λx. ↓ᵀ (f(a)) , where a = ↑ᵀ x and x is "fresh"
    
    ↑ᶜᵗˣ ∈ ⟦ Γ ⟧
    ↑∅ = tt
    ↑Γ,x:S = ↑Γ , ↑ᵀ x
    
    nf(t) = ↓ᵀ (⟦ t ⟧ ↑Γ)

In summary, the algorithm proceeds as follows:

  1) reflect the variables of the context `Γ` (`↑Γ`)

  2) interpret the value of the term using the environment
     of reflected variables (`⟦ t ⟧ ↑Γ`)

  3) "reify" the interpreted value of the term (`↓ᵀ (⟦ t ⟧ ↑Γ)`),
     returning it to a term in normal form

The "freshness" condition in this sketch is a key part of why we have not
started defining a more concrete version of the algorithm, but with this sketch
we can see how our new interpretation of the type `𝟙` has benefitted us: we are
able to evaluate a term, leaving its unknowns "untouched", and once we have
finished evaluating the term, we are easily able to convert it back into our
object language.

As an initial step in formally defining this algorithm, we can introduce the
rules for normal and neutral terms in Agda. Going forward, we will be using `𝓊`
(for "unknown") to refer to neutral terms and `𝓋` (for "value") to refer to
normal terms.

Neutral terms are normal terms in their blocked form. Variables are the "base
case" for blocked terms, with application of an unknown function to a normal
term also being blocked.

```agda
data Ne T Γ where
  ne-var : (x : Γ ∋ T)
           ------------
         → Ne T Γ (# x)

  ne-app : ∀ {S : Type} {𝓊 : Γ ⊢ S ⇒ T} {𝓋 : Γ ⊢ S}
         → Ne (S ⇒ T) Γ 𝓊
         → Nf S Γ 𝓋
           --------------
         → Ne T Γ (𝓊 · 𝓋)
```

Normal terms are terms in their normal form. `unit` is a normal term, as is an
abstraction whose body is itself normalized. Any neutral term is also a normal
term.

```agda
data Nf where
  nf-unit : ∀ {Γ : Ctx} → Nf 𝟙 Γ unit

  nf-abs : ∀ {S T : Type} {Γ : Ctx} {𝓋 : Γ , S ⊢ T}
         → Nf T (Γ , S) 𝓋
           ------------------
         → Nf (S ⇒ T) Γ (ƛ 𝓋)

  nf-neutral : ∀ {T : Type} {Γ : Ctx} {𝓊 : Γ ⊢ T}
             → Ne T Γ 𝓊
               --------
             → Nf T Γ 𝓊
```

Now, we can discuss the issue of the freshness condition used when reifying at
function type. We are using a de Brujin index representation, so "freshness" is
given to us freely by extending the context. However, there is no context
anywhere in our definition of reification, so what context do we extend with the
fresh variable? This is actually an intentional decision for reification,
because of a problem that is more subtle: after we reflect the variable, it may
later be reified in a different context than it was created. Consider the
reification of a semantic object `f` with type `(S → T) → U`:

    ↓⁽ˢ  ⃕ ᵗ⁾  ⃕ ᵘ f = λx. ↓ˢ  ⃕ ᵗ (f(a)) , where a = ↑ᵘ x

The inner reification evaluates further:

    ↓ˢ  ⃕ ᵗ (f(a)) = λy. ↓ᵗ (f(a)(b)) , where b = ↑ˢ y

This example showcases the problem: when we reflected `x` into our meta
language, we had to (presumably) use some context `Γ` to produce the Agda expression `a` with the type `Nf T Γ`. But later, when we reify `f(a)(b)`, we will
get a term that is possibly using the variable `x`, but the term is now in a
different context: `Γ, y:S`.

This suggests that we need to generalize our reflection of terms in the object
language over all contexts, so that at reification we can use a different
context than the one that was used at reflection.

It will be the case that we can only actually reify a semantic object using
a context that is an extension of the context used when that semantic object
was reflected into the meta language (and with the example above, the reason
is clear: our algorithm would otherwise not produce a term that is well-typed).

We introduce _liftable_ normal and neutral terms to address this. These are
normal/neutral terms that are generalized over contexts. That said, because we
cannot apply _any_ context to a liftable normal/neutral term, we will need a
placeholder value for some contexts.

```agda
-- Liftable neutral term
Ne^ : Type → Set
Ne^ T = ∀ (Γ : Ctx) → ∃[ t ] Ne T Γ t ⊎ ⊤

-- Liftable normal term
Nf^ : Type → Set
Nf^ T = ∀ (Γ : Ctx) → ∃[ t ] Nf T Γ t
```

For convenience, we only use this placeholder for liftable neutral terms.
This is possible because of how the algorithm for normalization by evaluation
is designed ─ reification always η-expands at function type, so there will only
ever be a need to use a placeholder value at our base type `𝟙`. In the case of
liftable normals, we can fallback to using `unit` (which is a valid normal term)
instead of using our placeholder value.

We allow ourselves this convenience because in proving the soundness of
normalization by evaluation, we will be proving that neither the placeholder
value nor the fallback of `unit` will actually be used.

Going forward, we will use `𝓋̂` and `𝓊̂` as the metavariables for liftable normal
terms and neutral terms respectively, and will append the symbol `^` for the
"liftable" counterpart of a language construct. For example, we define the
overloaded application `(𝓊̂ 𝓋̂)(Γ) = 𝓊̂(Γ)𝓋̂(Γ)` of liftable terms as `·^`.

```agda
_·^_ : ∀ {S T : Type} → Ne^ (S ⇒ T) → Nf^ S → Ne^ T
(𝓊̂ ·^ 𝓋̂) Γ with 𝓊̂ Γ
...           | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩ =
  let ⟨ 𝓋 , pf-𝓋 ⟩ = 𝓋̂ Γ in
  inj₁ ⟨ 𝓊 · 𝓋 , ne-app pf-𝓊 pf-𝓋 ⟩
...           | inj₂ tt           = inj₂ tt
```

The actual interpretation of the base type `𝟙` will in fact be an extension to
Agda's unit type that embeds liftable neutrals: `⊤̂` (pronounced "top hat"). With
it defined, we can also define the interpretation of types, along with
the evaluation of terms. These are exactly as was shown earlier in pseudocode.

```agda
data ⊤̂ : Set where
  unit : ⊤̂
  ne   : Ne^ 𝟙 → ⊤̂

instance
  ⟦Type⟧ : Interpretation Type
  Interpretation.⟦ ⟦Type⟧ ⟧ 𝟙 = ⊤̂
  Interpretation.⟦ ⟦Type⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧

env-lookup : ∀ {Γ : Ctx} {T : Type} → Γ ∋ T → ⟦ Γ ⟧ → ⟦ T ⟧
env-lookup {Γ , T} 𝑍     ⟨ _ , a ⟩ = a
env-lookup {Γ , T} (𝑆 x) ⟨ ε , _ ⟩ = env-lookup x ε

⟦⊢_⟧ : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → ⟦ Γ ⟧ → ⟦ T ⟧
⟦⊢ unit ⟧ _  = unit
⟦⊢ # x ⟧ ε   = env-lookup x ε
⟦⊢ ƛ t ⟧ ε a = ⟦⊢ t ⟧ ⟨ ε , a ⟩
⟦⊢ r · s ⟧ ε = ⟦⊢ r ⟧ ε (⟦⊢ s ⟧  ε)
```

We want a way to reify Agda expressions of type `⊤̂`, for which we will define a
function `↓⊤̂`. It is here that the fallback to `unit` happens, when the context
that the embedded liftable neutral is being lifted to results in it being
undefined. This case will be irrelevant and we will prove that it will never
actually be used in the algorithm for normalization by evaluation by proving
that the algorithm preserves the meaning of the original term.

```agda
↓⊤̂ : ⟦ 𝟙 ⟧ → Nf^ 𝟙
↓⊤̂ unit = unit^ where
  unit^ = (λ _ → ⟨ unit , nf-unit ⟩)
↓⊤̂ (ne 𝓊̂) Γ with 𝓊̂ Γ
...            | inj₁ ⟨ 𝓊 , pf ⟩ = ⟨ 𝓊 , nf-neutral pf ⟩
...            | inj₂ tt         = ⟨ unit , nf-unit ⟩
```

Next up is perhaps the most important part of normalization by evaluation:
reflection and reification. These are mutually recursive, and will each be
defined by induction on the type `T`.

```agda

mutual
  ↑ᵀ : {T : Type} → Ne^ T → ⟦ T ⟧
  ↑ᵀ {𝟙} 𝓊̂ = ne 𝓊̂
  ↑ᵀ {S ⇒ T} 𝓊̂ a = ↑ᵀ (𝓊̂ ·^ 𝓋̂) where 𝓋̂ = ↓ᵀ a

  ↓ᵀ : {T : Type} → ⟦ T ⟧ → Nf^ T
  ↓ᵀ {𝟙} = ↓⊤̂
  ↓ᵀ {S ⇒ T} f Γ =
    let ⟨ 𝓋 , pf ⟩ = ↓ᵀ (f a) (Γ , S) in
    ⟨ ƛ 𝓋 , nf-abs pf ⟩
    where a = ↑ᵀ (𝓍̂ S Γ)
```

For reification at function type, we use the following function which creates a
"fresh" variable for a context `Γ`. With our de Brujin representation, the fresh
variable will just be the de Brujin index `𝑍`.

`𝓍̂` will be a liftable variable that can be used in a context that is an
extension of `Γ , x:S` (and is undefined otherwise). When lifted to an extension
`Γ′` of `Γ , x:S` we can apply the extension renaming to the de Brujin index `𝑍`
to obtain its corresponding index in the extended context.

```
  𝓍̂ : (S : Type) → Ctx → Ne^ S
  𝓍̂ S Γ Γ′
    with Γ′ ≤? (Γ , S)
  ...  | no _          = inj₂ tt
  ...  | yes pf        = inj₁ ⟨ # x , ne-var x ⟩ where x = ρ-≤ pf 𝑍
```

With these two functions in place, we can also define the reflection of a
context `Γ` into an environment, which will be the reflected environment over
which a typed term in the context `Γ` will be evaluated.

```agda
↑ᶜᵗˣ : ∀ (Γ : Ctx) → ⟦ Γ ⟧
↑ᶜᵗˣ ∅       = tt
↑ᶜᵗˣ (Γ , T) = ⟨ ↑ᶜᵗˣ Γ  , ↑ᵀ (𝓍̂ T Γ) ⟩
```

Finally, the algorithm for normalization by evaluation is as follows:

```agda
nbe : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → ∃[ t ] Nf T Γ t
nbe {Γ} t = ↓ᵀ (⟦⊢ t ⟧ (↑ᶜᵗˣ Γ)) Γ

nf : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → Γ ⊢ T
nf t = let ⟨ t′ , _ ⟩ = nbe t in t′
```

And here we have some examples of the algorithm in action, reusing an example
from earlier.

```agda
-- normal form of (λx. x) unit is unit
nf-ex1 : nf ex1 ≡ unit
nf-ex1 with ex1
...       | _   = refl
```

### Correctness

We wish for our algorithm for normalization by evaluation to be both complete
and sound. First, we include as a postulate the property that if terms are
definitionally equal, then they must have the same interpretation.

```agda
postulate
  ==→⟦≡⟧ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {ε : ⟦ Γ ⟧}
         → t == t′
         → ⟦⊢ t ⟧ ε ≡ ⟦⊢ t′ ⟧ ε
```

We consider our algorithm for normalization by evaluation complete if two terms
that are definitionally equal (and thus have the same meaning) have the same
normal form:

    Γ ⊢ t = t′ : T implies nf(t) = nf(t′)

Expanding out `nf` here gives us the following theorem:

    Γ ⊢ t = t′ : T ⇒ ↓ᵀ (⟦ t ⟧ ↑Γ) Γ = ↓ᵀ (⟦ t′ ⟧ ↑Γ) Γ

This follows directly from `Γ ⊢ t = t′ : T` implying that `⟦ t ⟧ = ⟦ t′ ⟧`.

```agda
completeness : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
             → t == t′
             → nf t ≡ nf t′
completeness {Γ} t==t′ rewrite ==→⟦≡⟧ {ε = ↑ᶜᵗˣ Γ} t==t′ = refl
```

As for the soundness properties that we want from this algorithm:

  - `Γ ⊢ nf(t) : T` (well-typedness)

      We are using an intrinsically typed representation of terms, so this
      property is given to us automatically

  - `⟦ nf(t) ⟧ = ⟦ t ⟧` (preservation of meaning)

      As discussed, equality of functional terms in Agda is undecidable, for
      which we have introduced definitional equality. Even proving that
      `Γ ⊢ nf(t) = t : T` is difficult, and we will have to use a
      logical relation to prove it in the following section

  - `nf(nf(t)) = nf(t)` (idempotency)

      This follows directly from the preservation of
      meaning and completeness properties of the algorithm:

      By the soundness property of preservation of meaning,
      we will have `Γ ⊢ nf t = t : T`, which will in turn imply
      `nf (nf t) = nf(t)` by the algorithm's completeness

### Soundness

To prove that the algorithm for normalization by evaluation implemented
preserves the meaning of a program, we will prove that a term is
definitionally equal to its normal form:

   Γ ⊢ t = nf(t) : T

In proving that a term is definitionally equal to its normal form, we will have
that `⟦ nf (t) ⟧ = ⟦ t ⟧`, as definitional equality implies semantic equality.
This new property we wish to prove expands to:

    Γ ⊢ t = ↓ᵀ a Γ, where a = ⟦ t ⟧ ↑Γ

To prove this, we will establish a logical relation `Γ ⊢ t : T Ⓡ a` between a
well-typed term `Γ ⊢ t : T` and a semantic object in our meta language
`a ∈ ⟦ T ⟧` such that it implies `Γ ⊢ t = ↓ᵀ a Γ : T`. Later, we will prove that
`Γ ⊢ t : T Ⓡ ⟦ t ⟧ ↑Γ` (which will then finish our proof), but we will focus on
the logical relation itself for now.

For defining the relation in Agda, we will need to first define some other
relations. The first such relation we define "lifts" definitional equality to
include liftable neutrals. If the liftable neutral can be lifted to the context
`Γ`, this is just definitional equality. Otherwise, the relation can never hold,
as there is no lifted term in the context to compare to.

```agda
_==^_ : {Γ : Ctx} {T : Type} → Γ ⊢ T → Ne^ T → Set
_==^_ {Γ} t 𝓊̂ with 𝓊̂ Γ
... | inj₁ ⟨ 𝓊 , _ ⟩   = t == 𝓊
... | inj₂ _           = ⊥
```

<!---
```
infix 3 _==^_
```
--->

Formally, this relation represents the condition `Γ ⊢ 𝓊 = 𝓊̂(Γ) : T`, meaning
that a term `𝓊` is definitionally equal to the liftable neutral `𝓊̂` lifted to
the context `Γ`.

The logical relation `Γ ⊢ t : T Ⓡ a` will be defined inductively on types. At
type `𝟙`, the relation is defined as:

      Γ ⊢ t : 𝟙 Ⓡ 𝓋̂ ⇔ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = 𝓋̂(Γ′) : 𝟙

In other words, `t` is logically related to a semantic object `𝓋̂ ∈ ⊤̂` if and
only the term is definitionally equal to `𝓋̂` when lifted to any context `Γ′`
that is an extension of `Γ`.

For this condition, we also need to define a relation lifting definitional
equality to the unit type with embedded liftable neutrals, as was done with
`_==^_`.

```agda
_==⊤̂_ : ∀ {Γ : Ctx} → Γ ⊢ 𝟙 → ⟦ 𝟙 ⟧ → Set
_==⊤̂_ {Γ} t unit   = t == unit
_==⊤̂_ {Γ} t (ne 𝓊̂) = t ==^ 𝓊̂
```

<!---
```
infix 3 _==⊤̂_
```
--->

With these in place, we can start defining the logical relation `Ⓡ` between
terms and semantic objects. For function types, the relation is defined as:

    Γ ⊢ r : S → T Ⓡ f ⇔ ∀ Γ′ ≤ Γ. Γ′ ⊢ s : S Ⓡ a ⇒ Γ′ ⊢ r s : T Ⓡ f(a)

The relation is written so that it sort of expands functions, reducing our proof
that a functional term in STLC is logically related to a function in Agda to
only having to prove that given related arguments, the functional term and the
function in Agda both produce related results. Again, this is generalized over
all extensions of the context `Γ`. While our final results will only be
concerned with the context `Γ`, to prove these results we will need the relation
to be strengthened in this way.

```agda
_Ⓡ_ : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → ⟦ T ⟧ → Set
_Ⓡ_ {Γ} {𝟙} t 𝓋̂ = ∀ {Γ′ : Ctx} → (Γ′≤Γ : Γ′ ≤ Γ) → Γ′≤Γ ≤⊢ t ==⊤̂ 𝓋̂
_Ⓡ_ {Γ} {S ⇒ T} r f =
    ∀ {Γ′ : Ctx}
    → (Γ′≤Γ : Γ′ ≤ Γ)
    → ∀ {s : Γ′ ⊢ S} {a : ⟦ S ⟧}
    → s Ⓡ a
      -------------------------
    → (Γ′≤Γ ≤⊢ r) · s Ⓡ f a
```

<!---
```
infix 4 _Ⓡ_
```
--->

As the logical relation between terms and semantic objects is defined using
definitional equality, it is transitive with respect to definitional equality.
This is the first lemma we will prove using equational reasoning for
definitional equality. As for most proofs related to the logical relation `Ⓡ`
between terms and semantic objects, we prove it by induction on types, and do a
case analysis at type `𝟙` on the semantic object `a ∈ ⊤̂`. The proof makes use of
a lemma whose proof has been omitted, `==-subst`: if two terms are
definitionally equal , the terms with the same substitution applied are still
definitionally equal.

```agda
==-subst : ∀ {Γ Δ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {σ : Sub Δ Γ}
           → t == t′
           → t [ σ ] == t′ [ σ ]
```

<!---
```agda

==-subst {σ = σ} (β {t = t} {s})
  rewrite sub-sub {τ = σ} {id ∷ s} {t} =
  trans⁼⁼
    β
    (≡→==
      (trans
        (sub-sub {t = t})
        (cong-sub {t = t}
          (trans
            subst-zero-exts-cons
            (sym sub-dist))
          refl)))
==-subst {Γ} {T = S ⇒ T} {t} {σ = σ} η
  rewrite sub-sub {τ = exts σ} {↥ {T = S}} {t} =
  trans⁼⁼
    η
    (abs-compatible
      (app-compatible
        (≡→==
          (trans
            (sub-sub {τ = ↥} {σ} {t})
            (cong-sub {t = t} (extensionality λ{_ → sym rename-shift}) refl)))
        refl⁼⁼))
==-subst (abs-compatible t==t′) = abs-compatible (==-subst t==t′)
==-subst (app-compatible r==r′ s==s′) =
  app-compatible (==-subst r==r′) (==-subst s==s′)
==-subst refl⁼⁼ = refl⁼⁼
==-subst (sym⁼⁼ t==t′) = sym⁼⁼ (==-subst t==t′)
==-subst (trans⁼⁼ t₁==t₂ t₂==t₃) = trans⁼⁼ (==-subst t₁==t₂) (==-subst t₂==t₃)
```
--->

```agda
==-Ⓡ-trans : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {a : ⟦ T ⟧}
           → t == t′
           → t Ⓡ a
             -------
           → t′ Ⓡ a
==-Ⓡ-trans {T = 𝟙} {t} {t′} {unit} t==t′ pf Γ′≤Γ =
  begin==
    Γ′≤Γ ≤⊢ t′
  ==⟨ sym⁼⁼ (==-subst t==t′) ⟩
    Γ′≤Γ ≤⊢ t
  ==⟨ pf Γ′≤Γ ⟩
    unit
  ==∎
==-Ⓡ-trans {T = 𝟙} {t} {t′} {ne 𝓊̂} t==t′ pf {Γ′} Γ′≤Γ
  with 𝓊̂ Γ′          | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩ | t==𝓊    =
  begin==
    Γ′≤Γ ≤⊢ t′
  ==⟨ sym⁼⁼ (==-subst t==t′) ⟩
    Γ′≤Γ ≤⊢ t
  ==⟨ t==𝓊 ⟩
    𝓊
  ==∎
==-Ⓡ-trans {T = S ⇒ T} {r} {r′} r==r′ pf Γ′≤Γ sⓇa =
  ==-Ⓡ-trans r·s==r′·s r·sⓇfa
  where
    r·s==r′·s = app-compatible (==-subst r==r′) refl⁼⁼
    r·sⓇfa = pf Γ′≤Γ sⓇa
```

Additionally, because we have defined the relation so that its implication holds
for all extensions of a context, we can "weaken" the logical relation
`Γ ⊢ t : T Ⓡ a` for all `Γ′ ≤ Γ`, having that `Γ′ ⊢ t : T Ⓡ a` holds as well.
For this proof, we use another lemma, `weaken-compose`, whose proof has also
been omitted: weakening a term `t` twice is equivalent to weakening it once with
a composed weakening substitution.

<!---
```agda
ρ-≤-compose : ∀ {Γ″ Γ′ Γ : Ctx} {T : Type}
            → (Γ″≤Γ′ : Γ″ ≤ Γ′)
            → (Γ′≤Γ : Γ′ ≤ Γ)
            → (x : Γ ∋ T)
            → ρ-≤ Γ″≤Γ′ (ρ-≤ Γ′≤Γ x) ≡ ρ-≤ (≤-trans Γ″≤Γ′ Γ′≤Γ) x
ρ-≤-compose ≤-id ≤-id _                    = refl
ρ-≤-compose (≤-ext _) ≤-id _               = refl
ρ-≤-compose ≤-id (≤-ext _) _               = refl
ρ-≤-compose (≤-ext Γ″≤Γ′) (≤-ext Γ′≤Γ) x
  rewrite ρ-≤-compose Γ″≤Γ′(≤-ext Γ′≤Γ) x  = refl

```
--->

```agda
weaken-compose : ∀ {Γ″ Γ′ Γ : Ctx} {T : Type}
               → (Γ″≤Γ′ : Γ″ ≤ Γ′)
               → (Γ′≤Γ : Γ′ ≤ Γ)
               → (t : Γ ⊢ T)
               → Γ″≤Γ′ ≤⊢ Γ′≤Γ ≤⊢ t ≡ (≤-trans Γ″≤Γ′ Γ′≤Γ) ≤⊢ t
```

<!---
```agda
weaken-compose Γ″≤Γ′ Γ′≤Γ t
  rewrite sub-sub {τ = weaken Γ″≤Γ′} {weaken Γ′≤Γ} {t} =
    cong-sub {t = t}
      (extensionality λ{x → cong #_ (ρ-≤-compose Γ″≤Γ′ Γ′≤Γ x)})
      refl
```
--->

```agda
Ⓡ-weaken : ∀ {Γ′ Γ : Ctx} {T : Type} {Γ′≤Γ : Γ′ ≤ Γ} {t : Γ ⊢ T} {a : ⟦ T ⟧}
      → t Ⓡ a
      → Γ′≤Γ ≤⊢ t Ⓡ a
Ⓡ-weaken {T = 𝟙} {Γ′≤Γ} {t} pf Γ″≤Γ′
  rewrite weaken-compose Γ″≤Γ′ Γ′≤Γ t = pf (≤-trans Γ″≤Γ′ Γ′≤Γ)
Ⓡ-weaken {T = S ⇒ T} {Γ′≤Γ} {t} pf Γ″≤Γ′ sⓇa
  rewrite weaken-compose Γ″≤Γ′ Γ′≤Γ t = pf (≤-trans Γ″≤Γ′ Γ′≤Γ) sⓇa
```

The logical relation between terms and semantic objects is "sandwiched" between
reflection and reification -- to arrive at a logical relation between a term and
a semantic object, the semantic object must be a reflection of a liftable
neutral that is definitionally equal to the term. Likewise, if a logical
relation holds between a term and a semantic object, then the term must be
definitionally equal to the reification of that semantic object.

This is intentional, as these results will be exactly what we will need to prove
the soundness of normalization by evaluation. We formalize them with the
following lemmas, which we will prove mutually (as reflection and reification
are themselves defined mutually) by induction on types.

The first lemma is that if the liftable variable `𝓊̂` is definitionally equal
to a term `𝓊` for all contexts `Γ′ ≤ Γ`, then `𝓊` is logically related to the
reflection of `𝓊̂`:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ′) : T) ⇒ Γ ⊢ 𝓊 : T Ⓡ ↑ᵀ 𝓊̂

```agda
==^→Ⓡ↑ : ∀ {Γ : Ctx} {T : Type} {𝓊 : Γ ⊢ T} {𝓊̂ : Ne^ T}
        → (∀ {Γ′ : Ctx}
           → (Γ′≤Γ : Γ′ ≤ Γ)
           → Γ′≤Γ ≤⊢ 𝓊 ==^ 𝓊̂)
          -------------------
        → 𝓊 Ⓡ (↑ᵀ 𝓊̂)
```

A consequence of this lemma is that `Γ , x:T ⊢ x Ⓡ ↑ᵀ 𝓍̂ Γ`, which we can
define in Agda now as it will be necessary for proving the next lemma we will
introduce.

```agda
xⓇ↑ᵀ𝓍̂ : ∀ {Γ : Ctx} {T : Type}
        -------------------------
      → # 𝑍 {Γ} {T} Ⓡ ↑ᵀ (𝓍̂ T Γ)
```

The second lemma is that if `Γ ⊢ t : T` and `a ∈ ⟦ T ⟧` are logically related,
then `t` is definitionally equal to the reification of `a` for all contexts
`Γ′ ≤ Γ`:

    Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ′ : T

```agda
Ⓡ→==↓ : ∀ {Γ′ Γ : Ctx} {T : Type} {t : Γ ⊢ T} {a : ⟦ T ⟧}
      → t Ⓡ a
        ----------------------------
      → (Γ′≤Γ : Γ′ ≤ Γ)
      → Γ′≤Γ ≤⊢ t == proj₁ (↓ᵀ a Γ′)
```

This lemma is in fact what we wanted in the first place: that if a term is
logically related to a semantic object, then it is definitionally equal to the
reification of said object. It is stronger than we need it to be, but again this
is necessary to actually prove the implication.

We will start by proving the first lemma, focusing on each case of the proof
separately, before moving on to proving the second lemma. Again, the first
lemma is:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : T) ⇒ Γ ⊢ 𝓊 : T Ⓡ ↑ᵀ 𝓊̂

We prove this by induction on the type `T`. At type `𝟙`, our proof is
immediate, as `Γ ⊢ u : 𝟙 Ⓡ ↑ᵘⁿⁱᵗ 𝓊̂` is defined as:

    ∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : 𝟙

Which is exactly our given proof.

```agda
==^→Ⓡ↑ {T = 𝟙} pf Γ′≤Γ = pf Γ′≤Γ
```

At type `S → T`, the proof is more complicated. We want to prove that:


    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : S → T) ⇒ Γ ⊢ 𝓊 : S → T Ⓡ ↑ˢ  ⃕ ᵗ 𝓊̂

By definition of `Ⓡ`, this expands to:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : S → T) ⇒
      ∀ Γ′ ≤ Γ. Γ′ ⊢ s Ⓡ a ⇒
        Γ′ ⊢ 𝓊 s Ⓡ (↑ˢ  ⃕ ᵗ 𝓊̂) a

This simplifies further by the definition of reflection:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : S → T) ⇒
      ∀ Γ′ ≤ Γ. Γ′ ⊢ s Ⓡ a ⇒
        Γ′ ⊢ 𝓊 s Ⓡ ↑ᵀ (𝓊̂ · ↓ˢ a)

Our induction hypothesis gives us that at type `T`, the following holds:

    (∀ Γ″ ≤ Γ′. Γ″ ⊢ 𝓊 s = (𝓊̂ · ↓ˢ a) Γ″) ⇒
        Γ′ ⊢ 𝓊 s Ⓡ ↑ᵀ (𝓊̂ · ↓ˢ a)

With our induction hypothesis, our new goal is to prove only that:

    ∀ Γ″ ≤ Γ′. Γ″ ⊢ 𝓊 s = (𝓊̂ · (↓ˢ a)) Γ″ : T

Note that `(𝓊̂ · (↓ˢ a)) Γ″` is equivalent to `𝓊̂(Γ″) · (↓ˢ a)(Γ″)` (application
of liftable neutrals is overloaded), so the final form of the property we have
to prove is:

    Γ″ ⊢ 𝓊 s = 𝓊̂(Γ″) · ↓ˢ a Γ″ : T

Using the definitional equality rule of compatibility for application, we need
only prove that:

    Γ″ ⊢ 𝓊 = 𝓊̂(Γ″) : S → T
    Γ″ ⊢ s = ↓ˢ a Γ″ : S

The first property is our given evidence. We can use our other given proof (that
`Γ′ ⊢ s : S Ⓡ a`) with the the second lemma we will be proving to prove the
second property:

    Γ′ ⊢ s : T Ⓡ a ⇒ ∀ Γ″ ≤ Γ′. Γ″ ⊢ s = ↓ᵀ a Γ″ : T

```agda
==^→Ⓡ↑ {T = _ ⇒ _} {𝓊} {𝓊̂} pf {Γ′} Γ′≤Γ {s} {a} sⓇa =
  ==^→Ⓡ↑ 𝓊·s==𝓊̂·↓ˢa
    where
      𝓊·s==𝓊̂·↓ˢa : ∀ {Γ″ : Ctx}
                 → (Γ″≤Γ′ : Γ″ ≤ Γ′)
                 → Γ″≤Γ′ ≤⊢ (Γ′≤Γ ≤⊢ 𝓊) · s ==^ 𝓊̂ ·^ (↓ᵀ a)
      𝓊·s==𝓊̂·↓ˢa  {Γ″} Γ″≤Γ′
        with 𝓊̂ Γ″           | pf (≤-trans Γ″≤Γ′ Γ′≤Γ)
      ... | inj₁ ⟨ 𝓊″ , _ ⟩ | 𝓊==𝓊″                   =
        begin==
          Γ″≤Γ′ ≤⊢ (Γ′≤Γ ≤⊢ 𝓊) · s
        ==⟨ app-compatible (≡→== (weaken-compose Γ″≤Γ′ Γ′≤Γ 𝓊)) refl⁼⁼ ⟩
          (Γ″≤Γ ≤⊢ 𝓊) · (Γ″≤Γ′ ≤⊢ s)
        ==⟨ app-compatible 𝓊==𝓊″ refl⁼⁼ ⟩
          𝓊″ · (Γ″≤Γ′ ≤⊢ s)
        ==⟨ app-compatible refl⁼⁼ s==↓ᵀaΓ″ ⟩
          𝓊″ · proj₁ (↓ᵀ a Γ″)
        ==∎
        where
          s==↓ᵀaΓ″ = Ⓡ→==↓ sⓇa Γ″≤Γ′
          Γ″≤Γ = ≤-trans Γ″≤Γ′ Γ′≤Γ
```

This brings us to our second lemma:

    Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ′ : T

It will similarly be proven by induction on the type `T`. First, let us prove
the lemma for the type `𝟙`. At type `𝟙`, our lemma simplifies (by definition
of `Ⓡ`) to:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ t : T = a (Γ′)) ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵘⁿⁱᵗ a Γ′ : T

We can break this down further into a case analysis on `a`, which can be either
`unit` or an embedded liftable neutral `𝓊̂`. In both cases, we can use our given
proof.

```agda
Ⓡ→==↓ {T = 𝟙} {a = unit} pf with ↓ᵀ {𝟙} unit
... | _ = pf
Ⓡ→==↓ {Γ′} {T = 𝟙} {a = ne 𝓊̂} pf Γ′≤Γ
  with 𝓊̂ Γ′           | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩  | t==𝓊 = t==𝓊
```

For the case where we are at a function type `S → T`, our lemma now simplifies
to:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ x : S Ⓡ a ⇒ Γ′ ⊢ t x : T Ⓡ f a) ⇒
      ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ˢ  ⃕ ᵗ f Γ′

We can once again expand out the definition of reification at type `S → T`,
simplifying the lemma to:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ x : S Ⓡ a ⇒ Γ′ ⊢ t x : T Ⓡ f a) ⇒
      Γ′ ⊢ t = λx. ↓ᵀ f a (Γ′ , x:S) : T (where a = ↑ˢ 𝓍̂ Γ′)

We prove this by η-expanding `t` to `λx. t x` and then using the compatibility
rule for abstractions to simplify our goal to proving:

      Γ′ , x:S ⊢ t x = λx. ↓ᵀ f a (Γ′ , x:S) : T

Our inductive hypothesis gives us that:

      ∀ Γ″ ≤ Γ′. Γ″ ⊢ t x = ↓ᵀ f a : T

With it, all we need to prove is:

    Γ′ , x : S ⊢ t x : T Ⓡ f a

Our given proof further simplifies this goal to simply proving that
`∀ Γ″ ≤ Γ′. Γ″ ⊢ x : S Ⓡ a`. We have been using `a` for simplicity, but again,
`a = ↑ˢ 𝓍̂ Γ′`. Earlier, we established a lemma `xⓇ↑ᵀ𝓍̂` that was a special case
of the first lemma that we are proving mutually, and here we can use that lemma
to finish our proof.

```agda
Ⓡ→==↓ {Γ′} {T = S ⇒ _} {t} {f} pf Γ′≤Γ =
  begin==
    Γ′≤Γ ≤⊢ t
  ==⟨ η ⟩
    ƛ (S ↥⊢ Γ′≤Γ ≤⊢ t) · # 𝑍
  ==⟨
    abs-compatible (
      begin==
        (S ↥⊢ Γ′≤Γ ≤⊢ t) · # 𝑍
      ==⟨ app-compatible subst-lemma refl⁼⁼ ⟩
        (≤-ext Γ′≤Γ ≤⊢ t) [ id ] · # 𝑍
      ==⟨ Ⓡ→==↓ (pf (≤-ext Γ′≤Γ) xⓇa) ≤-id ⟩
        proj₁ (↓ᵀ (f a) (Γ′ , S))
      ==∎
  )⟩
    proj₁ (↓ᵀ f Γ′)
  ==∎
  where
    a = ↑ᵀ {S} (𝓍̂ S Γ′)
    xⓇa = xⓇ↑ᵀ𝓍̂ {Γ′} {S}

    subst-lemma =
      ≡→== (trans
             (sub-sub {τ = ↥} {weaken Γ′≤Γ} {t})
             (sym [id]-identity))
```

Lastly, we can quickly derive the lemma `Γ , x:T ⊢ x : T Ⓡ ↑ᵀ 𝓍̂ Γ` used in the
previous lemma using `(∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ′) : T) ⇒ Γ ⊢ 𝓊 Ⓡ ↑ᵀ 𝓊̂`. The proof requires an additional lemma, `≤-pf-irrelevance`, stating that any proof of
context extension is equivalent.

```agda
≤-pf-irrelevance : ∀ {Γ′ Γ : Ctx}
                 → (pf₁ : Γ′ ≤ Γ)
                 → (pf₂ : Γ′ ≤ Γ)
                 → pf₁ ≡ pf₂
≤-pf-irrelevance ≤-id ≤-id               = refl
≤-pf-irrelevance ≤-id (≤-ext pf)         = ⊥-elim (Γ≰Γ,T pf)
≤-pf-irrelevance (≤-ext pf) ≤-id         = ⊥-elim (Γ≰Γ,T pf)
≤-pf-irrelevance (≤-ext pf₁) (≤-ext pf₂)
  rewrite ≤-pf-irrelevance pf₁ pf₂       = refl
```

```agda
xⓇ↑ᵀ𝓍̂ {_} {T} = ==^→Ⓡ↑ x==𝓍̂ where
  x==𝓍̂ : ∀ {Γ Γ′ : Ctx}
       → (Γ′≤Γ,T : Γ′ ≤ Γ , T)
       → Γ′≤Γ,T ≤⊢ # 𝑍 ==^ 𝓍̂ T Γ
  x==𝓍̂ {Γ} {Γ′} pf
    with Γ′ ≤? (Γ , T)
  ... | no ¬pf                           = ¬pf pf
  ... | yes pf′
    with 𝓍̂ T Γ | ≤-pf-irrelevance pf pf′
  ... | _      | refl
    with ρ-≤ pf′ 𝑍
  ...| _                                 = refl⁼⁼
```

Let's focus on one of the lemmas we have proven:

    Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ : T

We have defined our logical relation with the goal of having the following case
of this property:

    Γ ⊢ t : T Ⓡ a ⇒ Γ ⊢ t = ↓ᵀ a Γ : T

We now need to show that:

    Γ ⊢ t : T Ⓡ ⟦t⟧ ↑Γ

With this, we can arrive at the definitional equality of a term and its normal
form as obtained from our algorithm for normalization by evaluation:

    Γ ⊢ t = ↓ᵀ (⟦t⟧ ↑Γ) Γ : T

To prove `Γ ⊢ t : T Ⓡ ⟦t⟧ ↑Γ`, we will need to extend our logical relation to
include substitutions and environments.

A parallel substitution `Γ ⊢ σ : Δ` will be logically related to an environment
`ε ∈ ⟦ Δ ⟧` if every term that the substitution `σ` is substituting for the
context `Δ` is logically related to the corresponding semantic object in the
environment `ε`. In Agda, we will use `Ⓡˢ` as `Ⓡ` is already reserved for terms
and semantic objects, though we will refer to the relation as `Γ ⊢ σ : Δ Ⓡ ε`.

```agda
_Ⓡˢ_ : ∀ {Γ Δ : Ctx} → Sub Γ Δ → ⟦ Δ ⟧ → Set
_Ⓡˢ_ {Δ = Δ} σ ε = ∀ {T : Type} → (x : Δ ∋ T) → σ x Ⓡ env-lookup x ε
```

<!---
```agda
infix 4 _Ⓡˢ_
```
--->

Similarly as for the logical relation between terms and semantic objects, if a
logical relation holds between a substitution and an environment, it holds for
any weakening of the substitution. The proof is immediate using `Ⓡ-weaken`.

```agda
Ⓡˢ-weaken : ∀ {Γ′ Γ Δ : Ctx} {Γ′≤Γ : Γ′ ≤ Γ} {σ : Sub Γ Δ} {ε : ⟦ Δ ⟧}
           → σ Ⓡˢ ε
           → σ ∘ (weaken Γ′≤Γ) Ⓡˢ ε
Ⓡˢ-weaken {Γ′≤Γ = Γ′≤Γ} σⓇε x = Ⓡ-weaken {Γ′≤Γ = Γ′≤Γ} (σⓇε x)
```

With the logical relation extended to substitutions and environments, we can
introduce the semantic typing judgement `Δ ⊨ t : T`. For any substitution
`Γ ⊢ σ : Δ` that is logically related to an environment `ε ∈ ⟦ Δ ⟧`,
`Γ ⊢ t [ σ ] : T` must be logically related to `⟦ t ⟧ ε`.

```agda
_⊨_ : ∀ {T : Type} → (Γ : Ctx) → Γ ⊢ T → Set
_⊨_ {T} Γ t =
  ∀ {Δ : Ctx} {σ : Sub Δ Γ} {ε : ⟦ Γ ⟧}
  → σ Ⓡˢ ε
    -------
  → t [ σ ] Ⓡ ⟦⊢ t ⟧ ε
```

Using the semantic typing judgement, we will be able to derive that
`Γ ⊢ t Ⓡ ⟦ t ⟧ ↑Γ`. By induction on the typing judgement `Δ ⊢ t : T`, we can
prove the semantic typing judgement `Δ ⊨ t : T` for a substitution `Γ ⊢ σ : Δ`
that is logically related to an environment `ε`; this is called the fundamental
lemma of logical relations.

For `unit`, the proof follows immediately from how we have defined the logical
relation between terms and semantic objects at type `𝟙`. In the case of
variables, the given proof is exactly what we need. Application follows from our
inductive hypotheses, leaving us at the abstraction case, which is the most
complicated to prove. Here are the first three cases:

```agda
fundamental-lemma : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
                  → Γ ⊨ t
fundamental-lemma {t = unit} σⓇε _ = refl⁼⁼
fundamental-lemma {t = # x} σⓇε = σⓇε x
fundamental-lemma {t = r · s} {σ = σ} σⓇˢε
  with fundamental-lemma {t = r} σⓇˢε | fundamental-lemma {t = s} σⓇˢε
... | Γ⊨r                              | Γ⊨s
  with Γ⊨r ≤-id Γ⊨s
... | pf
  rewrite [id]-identity {t = r [ σ ]} = pf
```

In the case of an abstraction `Γ ⊢ λx. t : S → T`, we want to prove:
    Γ ⊢ σ : Δ Ⓡ ε ⇒
      Γ ⊢ (λx. t) [ σ ] : S → T Ⓡ ⟦ Γ ⊢ λx. t : S → T ⟧ ε

By the definition of the application of a substitution to an abstraction, as
well as the definition of evaluation of an abstraction, this simplifies to:

    Γ ⊢ σ : Δ Ⓡ ε ⇒
      Γ ⊢ λx. t [ exts σ ] : S → T Ⓡ f
        (where f = λ a → ⟦ Γ , x: S ⊢ t : T ⟧ (ε , a))

We can also expand this using the definition of `Ⓡ` for functions (and
immediately reducing the application of `f` to `a`):

    Γ ⊢ σ : Δ Ⓡ ε ⇒
      ∀ Γ′ ≤ Γ. Γ′ ⊢ s : S Ⓡ a ⇒
        Γ′ ⊢ (λx. t [ exts σ ]) · s : T Ⓡ ⟦ Γ , x:S ⊢ t : T ⟧ (ε , a)

Already, this is a tricky property to parse. To start, we can use our lemma
that `Ⓡ` is transitive with respect to definitional equality, and use the `β`
rule to reduce `(λx. t [ exts σ ]) · s` to `t [ exts σ ] [ s / x ]`. Now, we
need only prove:

    Γ′ , x:S ⊢ t [ exts σ ] [ s / x ] : T Ⓡ ⟦ Γ , x:S ⊢ t : T ⟧ (ε , a)

Here, we can use a few substitution lemma to compose these two substitutions and
reduce them into just `σ ∷ s`, giving us:

    Γ′ , x:S ⊢ t [ σ ∷ s ] : T Ⓡ ⟦ Γ , x:S ⊢ t : T ⟧ (ε , a)

The property we want to show now looks like our induction hypothesis! Using the
induction hypothesis, we only need to show that:

     Γ′ , x:S ⊢ σ ∷ s : (Δ , x:S) Ⓡ (ε , a)

In other words, we need to prove that for any variable `x` in the context
`Δ , x : S` that `σ` is substituting a term for, the term being substituted for
that variable must be logically related to its corresponding semantic object in
the environment `(ε , a)`. We can do a case analysis on `x` to break this down
further. The first case is what the relation simplifies to in the case that the
variable being substituted for is `𝑍` ─ all that needs to be proven is that the
term being substituted for the first variable in `Δ , x : S` (which is `s`) is
logically related to the first semantic object in `(ε , a)`. In other words,
for this case, what needs to be proven is:

    Γ′ ⊢ s : S Ⓡ a

This is already our given proof, so this case follows immediately. The second
case is what the relation simplifies to in the case that the variable being
substituted for is in `Δ`, meaning `x` is `𝑆 x`:

    Γ′ ⊢ (σ ∷ s) (𝑆 x) : U Ⓡ env-lookup x ε

Here, we need to use a few substitution lemmas (which have been omitted as their
proofs are unrelated to the logical relation itself) to rewrite this to:

    Γ′ ⊢ σ x : U Ⓡ env-lookup x ε

This is again already given to us from our given proof that `Γ ⊢ σ : Δ Ⓡ ε`.
There is one small problem: we are now considering the context `Γ′` while our
given proof is over the context `Γ`. There was, in fact, an implict _weakening_
of `σ` in the changing of contexts (and it would be more correct to have been
writing `σ ∘ weaken Γ′≤Γ`, though the explanation used `σ` for simplicity).
Here, we can use the earlier lemma that if a substitution is logically related
to an environment, then so is a weakening of the substitution. With that, the
abstraction case is proven. Note that, in Agda, the expressions for
`t [ exts σ ]` and `σ ∷ s` are a little more complicated, mainly because of
the implicit weakening of the substitution `σ`.

```agda
fundamental-lemma {Γ} {S ⇒ T} {ƛ t} {σ = σ} {ε} σⓇε Γ′≤Γ {s} {a} sⓇa =
  ==-Ⓡ-trans (sym⁼⁼ β) t[exts-σ][s/x]Ⓡ⟦t⟧⟨ε,a⟩
  where
    t[exts-σ] = t [ exts σ ] [ exts (weaken Γ′≤Γ) ]
    σ∷s = exts σ ∘ exts (weaken Γ′≤Γ) ∘ (id ∷ s)
```

<!---
```agda
    subst-lemma₁ : ∀ {U : Type} {x : Γ ∋ U} → σ∷s (𝑆 x) ≡ (σ ∘ weaken Γ′≤Γ) x
    subst-lemma₁ {x = x} =
      begin
        σ∷s (𝑆 x)
      ≡⟨ sub-𝑆-shift {σ = σ∷s} {x} ⟩
        (↥ ∘ σ∷s) x
      ≡⟨⟩
        (↥ ∘ exts σ ∘ (exts (weaken Γ′≤Γ) ∘ (id ∷ s))) x
      ≡⟨ cong-app (cong-seq {σ = ↥ ∘ exts σ} refl subst-zero-exts-cons) x ⟩
        (↥ ∘ exts σ ∘ (weaken Γ′≤Γ ∷ s)) x
      ≡⟨ cong-app (cong-seq {σ = ↥} refl (cong-seq {σ = exts σ} exts-cons-shift refl)) x ⟩
        (↥ ∘ ((σ ∘ ↥) ∷ # 𝑍) ∘ (weaken Γ′≤Γ ∷ s)) x
      ≡⟨ cong-app (sym (sub-assoc {σ = ↥} {(σ ∘ ↥) ∷ # 𝑍} {weaken Γ′≤Γ ∷ s})) x ⟩
        ((↥ ∘ ((σ ∘ ↥) ∷ # 𝑍)) ∘ (weaken Γ′≤Γ ∷ s)) x
      ≡⟨ cong-app (cong-seq (sub-tail {s = # 𝑍} {σ ∘ ↥}) refl) x ⟩
        ((σ ∘ ↥) ∘ (weaken Γ′≤Γ ∷ s)) x
      ≡⟨ cong-app (sub-assoc {σ = σ} {↥} {weaken Γ′≤Γ ∷ s}) x ⟩
        (σ ∘ ↥ ∘ (weaken Γ′≤Γ ∷ s)) x
      ≡⟨ cong-app (cong-seq {σ = σ} refl (sub-tail {s = s} {weaken Γ′≤Γ})) x ⟩
        (σ ∘ weaken Γ′≤Γ) x
      ∎

    subst-lemma₂ = sub-sub {τ = id ∷ s} {exts (weaken Γ′≤Γ)} {t [ exts σ ]}
    subst-lemma₃ = sub-sub {τ = exts (weaken Γ′≤Γ) ∘ (id ∷ s)} {exts σ} {t}
```
--->

```agda
    σ∷sⓇ⟨ε,a⟩ : σ∷s  Ⓡˢ ⟨ ε , a ⟩
    σ∷sⓇ⟨ε,a⟩ 𝑍 = sⓇa
    σ∷sⓇ⟨ε,a⟩ (𝑆_ {T = U} x) rewrite subst-lemma₁ {x = x} =
      Ⓡˢ-weaken {Γ′≤Γ = Γ′≤Γ} σⓇε x

    t[exts-σ][s/x]Ⓡ⟦t⟧⟨ε,a⟩ : t[exts-σ] [ s ]₀ Ⓡ ⟦⊢ t ⟧ ⟨ ε , a ⟩
    t[exts-σ][s/x]Ⓡ⟦t⟧⟨ε,a⟩ rewrite subst-lemma₂ | subst-lemma₃ =
        fundamental-lemma {t = t} σ∷sⓇ⟨ε,a⟩
```

Separately, we have that the identity substitution is logically related to
our environment of reflected variables, `Γ ⊢ id : Γ Ⓡ ↑Γ`. We prove this by
induction on the variable being substituted for, using the lemma that
`Γ , x:T ⊢ x : T Ⓡ ↑ᵀ 𝓍̂ Γ` for the base case. For the inductive step, there is
a need to weaken the inductive hypothesis (which gives us that
`Γ ⊢ y : T Ⓡ ↑ᵀ 𝓍̂ Γ`) to the context `Γ , x:S`.

```agda
idⓇ↑Γ : ∀ {Γ : Ctx}
       → id Ⓡˢ (↑ᶜᵗˣ Γ)
idⓇ↑Γ 𝑍             = xⓇ↑ᵀ𝓍̂
idⓇ↑Γ {Γ , T} (𝑆 x) = Ⓡ-weaken {Γ′≤Γ = Γ,T≤Γ} {t = # x} (idⓇ↑Γ {Γ} x) where
  Γ,T≤Γ = ≤-ext {T = T} ≤-id
```

Now, we can arrive at the soundness of our algorithm for normalization by
evaluation. We have `Γ ⊢ id : Γ Ⓡ ↑Γ`, and using the fundamental lemma with
the identity substitution gives us:

    Γ ⊢ t [ id ] Ⓡ ⟦ t ⟧ ↑Γ

Note also that `t [ id ] ≡ t`. Using the lemma that a logical relation between a
term and a semantic object implies the definitional equality of the term to the
reification of the semantic object, we have:

    Γ ⊢ t = ↓ᵀ (⟦ t ⟧ ↑Γ) Γ : T

Thus, our algorithm for normalization by evaluation preserves the meaning of a
term that it normalizes. By extension, the algorithm is also idempotent (as we
have already shown it is complete), so the algorithm as a whole satisifies the
soundness properties we wanted.

```agda
nf-== : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
      → t == nf t
nf-== {Γ} {T} {t}
  with fundamental-lemma {t = t} (idⓇ↑Γ {Γ})
... | tⓇ⟦t⟧↑Γ
  with Ⓡ→==↓ tⓇ⟦t⟧↑Γ ≤-id
... | t==↓ᵀ⟦t⟧↑Γ
  rewrite [id]-identity {t = t [ id ]}
        | [id]-identity {t = t}                = t==↓ᵀ⟦t⟧↑Γ

nf-preserves-meaning : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T} {ε : ⟦ Γ ⟧}
                     → ⟦⊢ t ⟧ ε ≡ ⟦⊢ nf t ⟧ ε
nf-preserves-meaning {t = t} = ==→⟦≡⟧ (nf-== {t = t})

nf-idempotent : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
              → nf t ≡ nf (nf t)
nf-idempotent {t = t} = completeness (nf-== {t = t})
```

### Conclusion

In the end, we have formalized an algorithm in Agda for normalization by
evaluation that is based on the intuition of leaving the parts of a term that
cannot be evaluated (i.e. "unknowns") unchanged while still evaluating the parts
of the term that we do know how to reduce. The algorithm is both complete and
sound with respect to definitional equality, as we have proven. Completeness
followed quickly from the definition of the algorithm, while soundness required
a more in-depth proof involving the use of logical relations and their
fundamental lemma.

In his habilitation thesis, Andreas Abel goes on to introduce the algorithm for
the untyped lambda calculus, from which he continues to build upon, arriving at
an algorithm for a language with dependent types and a language with
impredicativity. This introduction to normalization to evaluation should
hopefully be a good starting point to explore these and other extensions of the
algorithm, such as simply trying out these proofs for yourself with a different
extension of the simply typed lambda calculus, or implementing the algorithm
in a language other than Agda.

#### Unicode

This site uses the following unicode in its Agda source code[^1]:

    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\Gl)
    ⊥  U+22A5  UP TACK (\bot)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊎  U+228E  MULTISET UNION (\u+)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ∃  U+2203  THERE EXISTS (\ex)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ¬  U+00AC  NOT SIGN (\neg)
    ≡  U+2261  IDENTICAL TO (\==)
    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ∀  U+2200  FOR ALL (\all)
    →  U+2192  RIGHTWARDS ARROW
    ‌≟  U+225F  QUESTIONED EQUAL TO (\?=)
    ∅  U+2205  EMPTY SET (\0)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    𝑍  U+1D44D  MATHEMATICAL ITALIC CAPITAL Z (\MiZ)
    Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG)
    𝑆  U+1D446  MATHEMATICAL ITALIC CAPITAL S (\MiS)
    ≤  U+2264  LESS-THAN OR EQUAL TO (\le)
    ′  U+2032  PRIME (\'1)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
    ⊢  U+22A2  RIGHT TACK (\|-)
    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·  U+00B7  MIDDLE DOT (\cdot)
    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs)
    Δ  U+0394  GREEK CAPITAL LETTER DELTA (\GD)
    ᵣ  U+1D63  LATIN SUBSCRIPT SMALL LETTER R (\_r)
    ↥  U+21A5  UPWARDS ARROW FROM BAR (\u-|)
    Σ  U+03A3  GREE CAPITAL LETTER SIGMA (\GS)
    ∘  U+2218  RING OPERATOR (\o)
    ω  U+03C9  GREEK SMALL LETTER OMEGA (\Go)
    ∷  U+2237  PROPORTION (\::)
    θ  U+03B8  GREEK SMALL LETTER THETA (\Gth)
    Φ  U+03A6  GREEK CAPITAL LETTER PHI (\Gf)
    ⟦  U+27E6  MATHEMATICAL LEFT WHITE SQUARE BRACKET (\[[)
    ⟦  U+27E7  MATHEMATICAL RIGHT WHITE SQUARE BRACKET (\]])
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb)
    η  U+03B7  GREEK SMALL LETTER ETA (\Gh)
    ∎  U+220E  END OF PROOF (\qed)
    ⦃  U+2983  LEFT WHITE CURLY BRACKET (\{{)
    ⦄  U+2984  RIGHT WHITE CURLY BRACKET (\}})
    𝓊  U+1D4CA  MATHEMATICAL SCRIPT SMALL U (\Mcu)
    𝓋  U+1D4CB  MATHEMATICAL SCRIPT SMALL V (\Mcv)
    ↑  U+2191  UPWARDS ARROW (\u)
    ᵀ  U+1D40  MODIFIER LETTER CAPITAL T (\^T)
    ↓  U+2193  DOWNWARDS ARROW (\d)
    ᶜ  U+1D9C  MODIFIER LETTER SMALL C (\^c)
    ᵗ  U+1D57  MODIFIER LETTER SMALL T (\^t)
    ˣ  U+02E3  MODIFIER LETTER SMALL X (\^x)
    ̂  U+0302  COMBINING CIRCUMFLEX ACCENT (\^)
    𝓍  U+1D4CD  MATHEMATICAL SCRIPT SMALL X (\Mcx)
    ≰  U+2270  NEITHER LESS THAN NOR EQUAL TO (\len)
    ₃  U+2083  SUBSCRIPT 3 (\_3)
    Ⓡ  U+24C7  CIRCLED LATIN CAPITAL LETTER R (\(r)2)
    ″  U+2033  DOUBLE PRIME (\'2)

#### References

[^1]: ̂ (`\^`) may be displayed on top of another character when written after it (e.g. `\Mcu\^` produces 𝓊̂)
