---
title: "Normalization by Evaluation"
author: Emmanuel Suárez Acevedo
---

### Background

This site is both an overview of normalization by evaluation and a formalization
in Agda of its presentation in Chapter 2 of Andreas Abel's habilitation thesis,
"Normalization by Evaluation: Dependent Types and Impredicativity" [@nbe]. It
was compiled from a literate Agda file available
[here](https://github.com/emmanueljs1/nbe/blob/main/NbE.lagda.md?plain=1)
by following the helpful advice in
[this](https://jesper.sikanda.be/posts/literate-agda.html) blog post by Jesper
Cockx.

For clarity and readability, some parts of the source file are left out in this
rendering, and this will be called out when possible. 

Some familiarity with Agda (e.g. such as having worked through the first part of
[Programming Languages Foundations in Agda](https://plfa.inf.ed.ac.uk/22.08/))
is assumed along with some knowledge of programming language foundations, though
the content is mostly self contained.

Note that, at the moment, some of the substitution lemmas used in the proof of
soundness are included only as postulates.

### Introduction

Consider the following term in the untyped lambda calculus:

    λx. (λy. y) x

This term is not in its *normal form*, that is, it can still undergo some
reductions. In this case, we can apply a beta reduction under the first binder
and arrive at:

    `λx. x`

With this new term being the normal form of `λx. (λy. y) x`. What we've just
done, believe it or not, is normalization by evaluation!

Normalization by evaluation is a technique for deriving the normal form of a
term in an object language by *evaluating* the term in a meta language (a
language we are using to describe the object language). In this case, our
object language was the untyped lambda calculus, and our meta language was,
well, just plain English.

In essence, you know how to reduce a term by evaluating the parts that can be
evaluated while leaving the parts that cannot untouched. That is the intuition
behind normalization by evaluation.

To actually formalize normalization by evaluation and prove its correctness in
Agda, the algorithm may seem to become less intuitive, but it will still be
based on this initial idea.

### Syntax

Before going into the algorithm itself, we will embed the language for which
we will be defining the algorithm: the simply-typed lambda calculus with unit as
a base type.

<!---
### Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open Eq using (refl; _≡_) renaming (sym to ≡-sym; trans to ≡-trans)
open Eq.≡-Reasoning using (_≡⟨⟩_; step-≡; begin_; _∎)

module NbE where
```
--->

We start off with the types: unit and functions.

```agda
data Type : Set where
  𝟙   : Type
  _⇒_ : ∀ (S T : Type) → Type

infixr 7 _⇒_
```

Additionally, we will want to have typing contexts for terms. A typing
context (for which we will use the metavariable `Γ`) is either the empty
context `∅` or an extension to a context `Γ , x:S` mapping an object
language variable to a type (here, `Γ` is extended with the variable
`x` mapped to the type 𝑆`).

Our Agda definition does not actually mention variable names at all, and
is really just a list of types. This is because we will be using a de
Brujin representation for variables, and the de Brujin index representing
a variable will be an index into the list of types that makes up a context.

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

Our de Brujin indices will actually be lookup judgements into a
context. They are very similar to natural numbers (and their contructors
have been named suggestively based on this similarity), though we define
them as such instead of simply using Agda's natural numbers both so that an
index into a context is well-defined and so that a variable can be intrinsically
typed, something that we will be taking advantage of in a moment.

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

Using these, we can represent the context `∅, x:S, y:T` along with the variable
names `"x"` and `"y"` as follows.

```agda
module Example (S T : Type) where
  ∅,x:S,y:T = ∅ , S , T

  x : ∅,x:S,y:T ∋ S
  x = 𝑆 𝑍

  y : ∅,x:S,y:T ∋ T
  y = 𝑍
```

Terms will be defined in our Agda formalization using an *intrinsically* typed
representation. We have defined our types first, and terms are only every
considered with respect to their type.

Using this representation, we only have to consider well-typed terms. An Agda
term `t` of type `Γ ⊢ T` is the well-typed STLC term `Γ ⊢ t : T` itself.

For clarity, when talking about terms we will not use their intrinsically typed
representation using de Brujin indices (e.g. the variable # 𝑍 will be referred
to as `Γ , x:T ⊢ x : T`)

```agda
data _⊢_ (Γ : Ctx) : Type → Set where
  unit : Γ ⊢ 𝟙

  #_ : ∀ {S : Type}
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
```

<!---
```
infix 4 _⊢_
infix 5 ƛ_
infixl 7 _·_
infix 9 #_
```
--->

We can define some sample programs in STLC using these constructors:

```agda
-- Γ ⊢ λx. x : T → T
ex0 : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T ⇒ T
ex0 = ƛ # 𝑍

-- ∅ ⊢ (λx. x) unit : 𝟙
ex1 : ∅ ⊢ 𝟙
ex1 = ex0 · unit
```

When defining the algorithm for normalization by evaluation, it will be
necessary to determine whether or not a context is an extension of
another. A context `Γ′` extends another context `Γ` if every mapping in
`Γ` is also in `Γ′`. In our representation, this will mean that if `Γ′`
extends `Γ`, then `Γ` is a "sublist" of `Γ′`. We inductively define the
rules for context extension based somewhat on this idea: a context extends
itself, and given that a context `Γ′` extends another context `Γ`, an
extension of `Γ′` is still an extension `Γ′`.

```agda
data _≤_ : Ctx → Ctx → Set where
  ≤-id : ∀ {Γ : Ctx} → Γ ≤ Γ

  ≤-ext : ∀ {Γ Γ′ : Ctx} {T : Type}
        → Γ′ ≤ Γ
          ----------
        → Γ′ , T ≤ Γ
```

<!---
```
infix 4 _≤_
```
--->

It will be helpful to make this relation decidable, for which we define a `≤?`.
To define it, equality between types and contexts will also need to be
decidable. Interestingly, because of how we've defined our relation, the typical
"obvious" case for a sublist relationship, that the empty list is a sublist of
any other list, has to be proven separately as a lemma in the form of `Γ≤∅`.

```agda
_≟Tp_ : ∀ (S T : Type) → Dec (S ≡ T)
𝟙         ≟Tp 𝟙                                    = yes refl
𝟙         ≟Tp (S ⇒ T)                              = no λ()
(S₁ ⇒ T₁) ≟Tp 𝟙                                    = no λ()
(S₁ ⇒ T₁) ≟Tp (S₂ ⇒ T₂) with S₁ ≟Tp S₂ | T₁ ≟Tp T₂
...                        | no ¬pf    | no _      = no λ{refl → ¬pf refl}
...                        | no ¬pf    | yes _     = no λ{refl → ¬pf refl}
...                        | yes _     | no ¬pf    = no λ{refl → ¬pf refl}
...                        | yes refl  | yes refl  = yes refl

_≟Ctx_ : (Γ Γ′ : Ctx) → Dec (Γ ≡ Γ′)

∅       ≟Ctx ∅                                  = yes refl
∅       ≟Ctx (_ , _)                            = no λ()
(_ , _) ≟Ctx ∅                                  = no λ()
(Γ′ , S) ≟Ctx (Γ , T) with Γ′ ≟Ctx Γ | S ≟Tp T
...                      | no ¬pf    | no _     = no λ{refl → ¬pf refl}
...                      | no ¬pf    | yes _    = no λ{refl → ¬pf refl}
...                      | yes _     | no ¬pf   = no λ{refl → ¬pf refl}
...                      | yes refl  | yes refl = yes refl

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
                           ≤-id       → Γ′≢Γ refl
                           (≤-ext pf) → ¬pf pf
```

Now that we have embedded the simply typed lambda calculus in Agda, we are
almost ready to start describing an algorithm for normalization by evaluation.
However, to prove properties concerning this algorithm, we will need to define
two more language constructs: substitutions and equality.

### Substitution

A parallel substitution `Γ ⊢ σ : Δ` provides a term in `Γ` to substitute for
each variable in the context `Δ` -- `Γ ⊢ σ : Δ` can be read as "`σ` is a
substitution for the context `Δ` using `Γ`". It is defined with the following
two rules:

                            Γ ⊢ σ : Δ       Γ ⊢ t : S
    ----------             --------------------------
    Γ ⊢ ∅ : ∅              Γ ⊢ (σ , x / s) : Δ , x:S

That is, any context can be used to substitute for the empty context (an "empty"
substitution), and any substitution can be extended with a well-typed term in
the substitution's "source" context. Really, this is building a substitution
based on the variables making up a context, where for each variable in the
context `Δ` (the context being substitutued for), there is a well-typed term
in the context `Γ` (the context being used for the substitution). With this
perspective, a substitution is a mapping (or a function) from variables in a
context to terms in another context.

```agda
Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀ {T : Type} → Δ ∋ T → Γ ⊢ T
```

To actually use a substitution, an operation is needed to actually apply the
substitution to a term in the context being used by the substitution:


    Δ ⊢ σ : Γ      Δ ⊢ t : T
    ------------------------
         Γ ⊢ t [ σ ] : T

This operation would allow for transforming a term `t` that is well-typed in
the context `Δ` using a substitution `σ` that maps every variable in `Δ` to a
term that is well-typed in `Γ`.

Defining this operation is actually a little tricky in Agda, because the
language requires all code that is written to be terminating. The typical
definition of the application of a substitution `σ` is not obviously
terminating. For this, defining a smaller subset of substitution will help:
renaming.

Renaming is a specialized substitution where the only terms that can be
substituted for variables are other variables (i.e. a renaming `Γ ⊢ ρ : Δ`
provides a variable in `Γ`, not a term in `Γ`, to replace for every variable
in `Δ`).

It is necessary to first to define renaming substitutions so that termination
is guaranteed.

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

Using renamings, we can start defining the building blocks that will allow us
to eventually get to a definition for the application of a substitution that is
guaranteed to be terminating.

There are two basic renamings: the identity renaming and the shifting renaming.
To indicate that these are renamings specifically (though their versions for
substitutions in general are nearly identical), the subscript `ᵣ` is used.

```agda
idᵣ : ∀ {Γ : Ctx} → Ren Γ Γ
idᵣ x = x

↥ᵣ : ∀ {Γ : Ctx} {T : Type} → Ren (Γ , T) Γ
↥ᵣ x = 𝑆 x
```

Any two renamings can also be composed.

```agda
_∘ᵣ_ : ∀ {Γ Δ Σ : Ctx} → Ren Δ Γ → Ren Σ Δ → Ren Σ Γ
ρ ∘ᵣ ω = λ x → ω (ρ x)
```

<!---
```agda
infixr 9 _∘ᵣ_
```
--->

Composing renamings, it is possible to define a renaming for a context `Γ′`
using a context that it extends, `Γ`. Really, this renaming is the building
up of many compositions of the shifting renaming, ending finally at the identity
renaming.

```
weakenᵣ : ∀ {Γ′ Γ : Ctx} → Γ′ ≤ Γ → Ren Γ′ Γ
weakenᵣ ≤-id = idᵣ
weakenᵣ (≤-ext pf) = weakenᵣ pf ∘ᵣ ↥ᵣ
```

The application of a renaming substituion `Γ ⊢ ρ : Δ` to a term `Δ ⊢ t : T`
rebases the term to the context `Γ`. This is done by "distributing" the
renaming substitution across all subterms of the term, renaming all variables
used in the term with their corresponding variable in `Γ`.

```agda
ext : ∀ {Γ Δ : Ctx} {T : Type} → Ren Γ Δ → Ren (Γ , T) (Δ , T)
ext ρ 𝑍 = 𝑍
ext ρ (𝑆 x) = 𝑆 ρ x

_[_]ᵣ : ∀ {Γ Δ : Ctx} {T : Type}
      → Δ ⊢ T
      → Ren Γ Δ
        -------
      → Γ ⊢ T
unit [ _ ]ᵣ = unit
# x [ ρ ]ᵣ = # ρ x
(ƛ t) [ ρ ]ᵣ = ƛ t [ ext ρ ]ᵣ
(r · s) [ ρ ]ᵣ = r [ ρ ]ᵣ · s [ ρ ]ᵣ
```

<!---
```agda
infix 8 _[_]ᵣ
```
--->

With the application of a renaming substitution, it is now possible to define
the application of any general substitution such that it is guaranteed to
terminate. It was necessary because to extend the application of a substitution
under a binder, a shifting renaming needs to be applied to all of the terms
in the substitution.

```agda
exts : ∀ {Γ Δ : Ctx} {T : Type}
     → Sub Γ Δ
       -------------
     → Sub (Γ , T) (Δ , T)
exts σ 𝑍     = # 𝑍
exts σ (𝑆 x) = (σ x) [ ↥ᵣ ]ᵣ
```

Now, we can actually define the application `t [ σ ]` of a parallel substitution
`Γ ⊢ σ : Δ` to a term `Δ ⊢ t : T`, and Agda believes that the definition is
terminating. It is very similar to the application of a renaming substitution,
except now we are replacing variables with entire terms.

```agda

_[_] : ∀ {Γ Δ : Ctx} {T : Type}
     → Δ ⊢ T
     → Sub Γ Δ
       -------
     → Γ ⊢ T
unit [ _ ] = unit
# x [ σ ] = σ x
(ƛ t) [ σ ] = ƛ t [ exts σ ]
(r · s) [ σ ] = r [ σ ] · s [ σ ]
```

<!---
```
infix 8 _[_]
```
--->

As for renaming substitutions, there is a more general identity substitution and
shifting substitution, and parallel substitutions can be composed by applying a substitution `Γ ⊢ τ : Δ` to every term in a substitution `Δ ⊢ σ : Σ`.

```agda
id : ∀ {Γ : Ctx} → Sub Γ Γ
id x = # x

↥ : ∀ {Γ : Ctx} {T : Type} → Sub (Γ , T) Γ
↥ x = # 𝑆 x

_∘_ : ∀ {Γ Δ Σ : Ctx} → Sub Δ Γ → Sub Σ Δ → Sub Σ Γ
(σ ∘ τ) x = (σ x) [ τ ]
```

<!---
```agda
infixr 9 _∘_
```
--->

Using the renaming substitution, any well-typed term in `Γ` can be "weakened"
to a well-typed term in a context `Γ′`. As shorthand, `_≤⊢_` will be used for
the application of a weakening substitution (and in Agda, this will look a lot
like an extended judgement: `Γ′≤Γ ≤⊢ t`).

```agda
weaken : ∀ {Γ′ Γ : Ctx}
       → Γ′ ≤ Γ
         --------
       → Sub Γ′ Γ
weaken pf x = # weakenᵣ pf x

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

### Definitional Equality

We still have one language construct left to define -- equality. To explain
why we will need to define equality, we can first discuss normalization by
evaluation in more detail. Normalization by evaluation is an algorithm for
normalization. Normalization is the process of transforming a term into its
normal form. The normal form of a term is *unique*, being the term with all
possible reductions (i.e. "computations") applied to it. For any normalization
algorithm `nf` such that `nf(t)` is the normal form of a term `Γ ⊢ t : T`, we
would expect the following properties to hold.

  - `Γ ⊢ nf(t) : T` (well-typedness of normal form)

    A normalization algorithm should still produce a term that is well-typed
    under the context `Γ` (and with the same type)

  - `nf(nf(t)) = nf(t)` (idempotency)

    This property refers to the "normalization" part of the algorithm ─ it
    should actually produce a term that has been fully normalized, i.e. it
    cannot undergo any more normalization.

  - `⟦ nf(t) ⟧ = ⟦ t ⟧` (preservation of meaning)

    The `⟦ t ⟧` notation here indicates the *denotation* of `t`, that is,
    the meaning of `t` (e.g. in some meta-language). Put simply, this property
    requires that normalizing a term should not change its expected behavior.

The last property is perhaps the trickiest, because equality of functions is
undecidable. Instead, we will want to use βη-equivalence, or _definitional
equality_. In STLC, we have that two terms are definitionally equal iff they
have the same meaning. By proving that `Γ ⊢ nf(t) = t : T`, that the normal form
of a term is definitionally equal to the original term, we will be proving that
the normal form of a term preserves the meaning of the original term.

To do so, we will need to actually define operations for β-reductions and
η-expansions.

A β-reduction will be the application of a substitution `t [ s / x ]` that is
essentially an extension to the identity substitution with the term `s` used
for the first term in the substitution. In Agda, we will use `_[_]₀` (as we are
replacing the zeroth term in the identity substitution) to represent a
β-reduction.

```agda
sub-zero : ∀ {Γ : Ctx} {S : Type} → Γ ⊢ S → Sub Γ (Γ , S)
sub-zero s 𝑍 = s
sub-zero _ (𝑆 x) = # x

_[_]₀ : ∀ {Γ : Ctx} {S T : Type}
  → Γ , S ⊢ T
  → Γ ⊢ S
    ---------
  → Γ ⊢ T
_[_]₀ {Γ} {S} t s = t [ sub-zero s ]
```

<!---
```
infix 8 _[_]₀
```
--->

η-expansion for a functional term `Γ ⊢ t : S → T` will be an abstraction
`Γ ⊢ λx . t x : S → T` containing the application of a variable `Γ , x:S ⊢ x :
S` to the term, which needs to have an incrementing substitution applied to it
as we are using an intrinsically-typed representation.

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

  β-ƛ : ∀ {Γ : Ctx} {S T : Type}
          {t : Γ , S ⊢ T}
          {s : Γ ⊢ S}
          ----------------------
        → (ƛ t) · s == t [ s ]₀

  -- Function extensionality, i.e. Γ ⊢ t = Γ ⊢ λx. t x : S ⇒ T
  η : ∀ {Γ : Ctx} {S T : Type}
        {t : Γ ⊢ S ⇒ T}
        ----------------------
      → t == η-expand t

  -- Compatibility rules
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
```

<!---
```
infix 3 _==_
```
--->

For the readability of some of our proofs, it will be helpful to have the
ability to use equational reasoning with respect to definitional equality. We
omit this definition, but it is almost identical to Agda's own equational
reasoning for propositional equality. It will also be helpful to include the
fact that propositional equality implies definitional equality.

<!---
```agda
module ==-Reasoning where

  infix  1 begin==_
  infixr 2 _==⟨_⟩_
  infix  3 _==∎

  begin==_ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
           → t == t′
             ---------
           → t == t′
  begin== pf = pf

  _==⟨_⟩_ : ∀ {Γ : Ctx} {T : Type} {t₂ t₃ : Γ ⊢ T}
          → (t₁ : Γ ⊢ T)
          → t₁ == t₂
          → t₂ == t₃
            -----
          → t₁ == t₃
  t₁ ==⟨ t₁≡t₂ ⟩ t₂≡t₃  =  trans t₁≡t₂ t₂≡t₃

  _==∎ : ∀ {Γ : Ctx} {T : Type} → (t : Γ ⊢ T)
         -----
       → t == t
  t ==∎  =  refl
```
--->

```agda
open ==-Reasoning public

≡→== : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
     → t ≡ t′
       -------
     → t == t′
≡→== pf rewrite pf = refl
```

### Evaluation

The evaluation, or interpretation, `⟦ t ⟧` of a well-typed term `Γ ⊢ t : T`
assigns a meaning to `t` by equating it to a semantic object in our meta
language, using an interpretation of the context `Γ` (an _environment_)
under which the term `t` is well-typed.

For types, we can interpret `𝟙` as Agda's own unit type, `⊤`, and functions as
Agda functions, defined inductively on their types.

    ⟦ 𝟙 ⟧ = ⊤
    ⟦ S ⇒ T ⟧ = ⟦ S ⟧ → ⟦ T ⟧

An empty context is interpreted as the unit type (an empty environment), and an
extension to a context is defined inductively, with the extension itself being
the interpretation of the type the context is extended with.

    ⟦ ∅ ⟧ = ⊤
    ⟦ Γ , S ⟧ = ⟦ Γ ⟧ × ⟦ S ⟧

From now on, we will use the metavariable ε to represent environments. The
interpretation of a variable expects an environment, and is essentially a
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
interpretations of types and contexts. For now, we are only including the
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
form of a term, but rather its meaning as a semantic object in our meta language.
An algorithm for normalization by evaluation would need a way to to convert a
semantic object in our meta language back into a term in the object language.

Instead, we want to evaluate (i.e. normalize) the parts of the expression that
actually _can_ be evaluated (such as function application), while leaving the
parts that cannot intact. Under this view, normalization by evaluation becomes
the evaluation of an expression with unknowns (i.e. variables) to another,
possibly simplified, expression with unknowns.

To get this behavior, we make a subtle change to the "meaning" of a term in the meta language -- instead of terms of type `𝟙` mapping to Agda's unit type, they
will now evaluate them terms in their normal form.

This is a subtle distinction with a significant impact on the algorithm we will
define. We can now easily convert back to the object language, because in
technicality we never left it to begin with.

More concretely, we will be mapping a term `Γ ⊢ t : T` to an Agda data
type used to represent a term in its normal form. Terms in their normal
form (normal terms) will be defined mutually with terms that are blocked
on evaluation because they are unknown (neutral terms).

```agda
data Nf : (T : Type) → (Γ : Ctx) → Γ ⊢ T → Set -- Normal terms
data Ne (T : Type) (Γ : Ctx) : Γ ⊢ T → Set     -- Neutral terms
```

Now, the interpretation of a term of type `𝟙` is what we will want it to be to
define a suitable algorithm for normalization by evaluation:

    ⟦ 𝟙 ⟧ = Nf 𝟙

Note that our definition of normal terms is indexed both by a type and a
context, yet here the interpretation of a type is only indexed by the type
itself. We will get to this later, but it is for this reason that we have
not yet written this implementation out in Agda. For now, we can give
an initial sketch of the algorithm, using a _reflection_ function `↑ᵀ` that
maps neutral terms of type `T` to semantic objects in `⟦ T ⟧`, and a
_reification_ function `↓ᵀ` for mapping a semantic object in `⟦ T ⟧` to normal
forms of type `T`:

Putting all of these pieces together, we can present (in pseudo-code)
what an algorithm for normalization by evaluation would do.

    ⟦ 𝟙 ⟧ = Nf 𝟙
    ⟦ S → T ⟧ = ⟦ S ⟧ → ⟦ T ⟧

    ↑ᵀ ∈ Ne T → ⟦ T ⟧
    ↑ᵘⁿⁱᵗ 𝓊 = 𝓊
    ↑ˢ⃗ᵗ 𝓊 (a ∈ ⟦ S ⟧) = ↑ᵀ (𝓊 𝓋) , 𝓋 = ↓ˢ a
    
    ↓ᵀ ∈ ⟦ T ⟧ → Nf T
    ↓ᵘⁿⁱᵗ 𝓋 = 𝓋
    ↓ˢ⃗ᵗ f = λx. ↓ᵀ (f(a)) , where a = ↑ᵀ x and x is "fresh"
    
    ↑ᶜᵗˣ ∈ ⟦ Γ ⟧
    ↑∅ = tt
    ↑Γ,x:S = ↑Γ , ↑ᵀ x
    
    nf(t) = ↓ᵀ (⟦ t ⟧ ↑Γ)

In summary, the algorithm proceeds as follows:

  1) reflect the variables of the context Γ (↑Γ)

  2) interpret the value of the term using the environment
     of reflected variables (`⟦ t ⟧ ↑Γ`)

  3) "reify" the interpreted value of the term (`↓ᵀ (⟦ t ⟧ ↑Γ)`),
     returning it to a term in normal form

The "freshness" condition is a key part of why we have not started
defining a more concrete version of the algorithm, but with this sketch we
can see how our new interpretation of the type `𝟙` has benefitted us: we are
able to evaluate a term, leaving its unknowns "untouched", and once we have
finished evaluating the term, we are able to convert it back into our object
language.

As an initial step in formally defining this algorithm, we can introduce
the rules for normal and neutral terms in Agda. Going forward, we will be
using 𝓊 (for "unknown") to refer to neutral terms and 𝓋 (for "value") to
refer to normal terms.

Neutral terms are normal terms in their blocked form. Variables are the "base
case" for blocked terms, with application on an unknown function to a normal
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

    ↓⁽ˢ⃗ᵗ⁾⃗ᵘ f = λx. ↓ˢ⃗ᵗ (f(a)) , where a = ↑ᵘ x

The inner reification evaluates further:

    ↓ˢ⃗ᵗ (f(a)) = λy. ↓ᵗ (f(a)(b)) , where b = ↑ˢ y

Herein lies our problem: when we reflected `x` into our meta language, we had to
use some context `Γ` to produce the Agda expression `a` with (presumably), the
type `Nf T Γ`. Later, when we reify `f(a)(b)`, we will arrive at a term that is
possibly using the variable `x`, but we are now in a different context,
`Γ, y:S`. This suggests that we need to generalize our reflection of terms in
the object language over all contexts, so that at reification we can use
a different context than the one that was used at reflection.

It will be the case that we can only actually reify a semantic object using
a context that is an extension of the context used when that semantic object
was reflected into the meta language (and with the example above, the reason
is clear: our algorithm would otherwise not produce a term that is well-typed).

We introduce liftable normal and neutral terms to address this. These are
normal/neutral terms that are generalized over contexts. Because we cannot
apply _any_ context to a liftable normal/neutral term, we will need a
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
is designed ─ reification always eta-expands at function type, so there will
only ever be a need to use a placeholder value at our base type `𝟙`. In the case
of liftable normals, we can fallback to using `unit` (which is a valid normal
term) instead of using our placeholder value. We allow ourselves this
convenience because in proving the soundness of normalization by evaluation,
we will be proving that neither the placeholder value nor the fallback of `unit`
will actually be used.

Going forward, we will use 𝓋̂ and 𝓊̂ as the metavariables for liftable normal
terms and neutral terms respectively, and will append the symbol ^ for the
"liftable" counterpart of a System T construct. For example, we define the
overloaded application `(𝓊̂ 𝓋̂)(Γ) = 𝓊̂(Γ)𝓋̂(Γ)` of liftable terms as `_·^_`.

```agda
_·^_ : ∀ {S T : Type} → Ne^ (S ⇒ T) → Nf^ S → Ne^ T
(𝓊̂ ·^ 𝓋̂) Γ with 𝓊̂ Γ
...           | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩ =
  let ⟨ 𝓋 , pf-𝓋 ⟩ = 𝓋̂ Γ in
  inj₁ ⟨ 𝓊 · 𝓋 , ne-app pf-𝓊 pf-𝓋 ⟩
...           | inj₂ tt           = inj₂ tt
```

The actual interpretation of the base type `unit` will in fact be an extension
to Agda's unit type that embeds liftable neutrals, `⊤̂` (pronounced "top hat").

```agda
data ⊤̂ : Set where
  unit : ⊤̂
  ne   : Ne^ 𝟙 → ⊤̂

instance
  ⟦Type⟧ : Interpretation Type
  Interpretation.⟦ ⟦Type⟧ ⟧ 𝟙 = ⊤̂
  Interpretation.⟦ ⟦Type⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧
```

Evaluation can now actually be defined in Agda, having been blocked by a lack of
an interpretation for types. It is exactly as was shown earlier in pseudo-code.

```agda
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
function `↓⊤̂`. It is here that given an incompatible context that results in the
embedded liftable neutral being undefined, it will be necessary fallback to
`unit`. Once again, this case will be irrelevant and we will prove that it will
never actually be used in the algorithm for normalization by evaluation.

```agda
↓⊤̂ : ⟦ 𝟙 ⟧ → Nf^ 𝟙
↓⊤̂ unit = unit^ where
  unit^ = (λ _ → ⟨ unit , nf-unit ⟩)
↓⊤̂ (ne 𝓊̂) Γ with 𝓊̂ Γ
...            | inj₁ ⟨ 𝓊 , pf ⟩ = ⟨ 𝓊 , nf-neutral pf ⟩
...            | inj₂ tt         = ⟨ unit , nf-unit ⟩
```


Next up is perhaps the most important part of normalization by evaluation,
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
"fresh" variable for a context `Γ`. Really, this is just the de Brujin index `𝑍`
for a context `Γ, x:S`. This will be a liftable variable that can be used in
a context that is an extension of `Γ, x:S` (and is undefined otherwise). When
applied to an extension `Γ′` of `Γ, x:S` we can apply the weakening renaming to
the de Brujin index `𝑍` to obtain its corresponding index in the extended
context.

```
  𝓍̂ : (S : Type) → Ctx → Ne^ S
  𝓍̂ S Γ Γ′
    with Γ′ ≤? (Γ , S)
  ...  | no _          = inj₂ tt
  ...  | yes pf        = inj₁ ⟨ # x , ne-var x ⟩ where x = weakenᵣ pf 𝑍
```

With these two functions in place, we can also define the reflection of a
context `Γ` into an environment. This will be the reflected environment over
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
and sound. We will describe exactly what this means, but it is for the purpose
of proving these properties that we introduced definitional equality.
Specifically, we will need the property that if terms are definitionally equal,
then they must have the same interpretation. We include this property as a
postulate.

```agda
postulate
  ==→⟦≡⟧ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {ε : ⟦ Γ ⟧}
         → t == t′
         → ⟦⊢ t ⟧ ε ≡ ⟦⊢ t′ ⟧ ε
```

We consider our algorithm for normalization by evaluation if two terms that are
definitionally equal (and thus have the same meaning) have the same normal form:

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

Separately, the soundness properties that we want from this algorithm are the
following:

  - `Γ ⊢ nf(t) : T` (well-typedness)
      We are using an intrinsically typed
      representation of terms, so this property is
      given to us automatically

  - `⟦ nf(t) ⟧ = ⟦ t ⟧` (preservation of meaning)
      We want an algorithm for normalization by evaluation to ensure that the
      normal form of a term that is obtained is _semantically equal_ to the
      original term, i.e. the two terms have the same meaning. As discussed,
      equality of functional terms in Agda is undecidable, for which we have
      introduced definitional equality (which implies semantic equality). Even
      proving that `Γ ⊢ nf(t) = t : T` is difficult, and we will have to use a
      logical relation to prove it. We do so in the following section.

  - `nf(nf(t)) = nf(t)` (idempotency)
      This follows directly from the preservation of
      meaning and completeness properties of the algorithm:

      By the soundness property of preservation of meaning,
      we have `Γ ⊢ nf t = t : T`, which implies `nf (nf t) = nf(t)`
      by completeness

<!--

The following are lemmas that will be necessary for proving the definitional
equality of a term and its normal form as obtained by normalization by
evaluation.

First, a few properties about the `≤` relation, which are all required to prove
irrelevance of proof for the relation.

```agda
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
≤-trans : ∀ {Σ Δ Γ : Ctx}
        → Σ ≤ Δ
        → Δ ≤ Γ
          -------
        → Σ ≤ Γ
≤-trans ≤-id ≤-id = ≤-id
≤-trans ≤-id (≤-ext pf) = ≤-ext pf
≤-trans (≤-ext pf) ≤-id = ≤-ext pf
≤-trans (≤-ext pf₁) (≤-ext pf₂) = ≤-ext (≤-trans pf₁ (≤-ext pf₂))
```

Substitution / renaming lemmas, a lot of these are directly inspired by the
 σ algebra equations / σ algebra of substitutions in
[this](https://plfa.github.io/Substitution/) chapter of PLFA.

```agda
{-
sub-head : ∀ {Γ Δ : Ctx} {T : Type} {t : Γ ⊢ T} {σ : Sub Γ Δ}
         → # 𝑍 [ σ , t ] ≡ t
sub-head = refl

Z-shift : ∀ {Γ : Ctx} {S : Type}
        → (subst-incr , # 𝑍) ≡ subst-id {Γ , S}
Z-shift = refl

sub-dist : ∀ {Γ Δ Σ : Ctx} {S : Type} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {s : Δ ⊢ S}
         → (σ , s) ∘ τ ≡ (σ ∘ τ , s [ τ ])
sub-dist = refl

sub-app : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ} {S T : Type} {r : Δ ⊢ S ⇒ T} {s : Δ ⊢ S}
        → (r · s) [ σ ] ≡ r [ σ ] · s [ σ ]
sub-app = refl

cong-ext : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ} {T : Type}
         → ρ ≡ ρ′
          → _≡_ {A = Ren (Γ , T) (Δ , T)} (ρ ↥ᵣ , 𝑍) (ρ′ ↥ᵣ , 𝑍)
cong-ext ρ≡ρ′ rewrite ρ≡ρ′ = refl

cong-rename : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ} {T : Type} {t : Δ ⊢ T}
            → ρ ≡ ρ′
            → t [ ρ ]ᵣ ≡ t [ ρ′ ]ᵣ
cong-rename ρ≡ρ′ rewrite ρ≡ρ′ = refl

cong-exts : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ} {T : Type}
          → σ ≡ σ′
          → _≡_ {A = Sub (Γ , T) (Δ , T)} (σ ↥ , # 𝑍) (σ′ ↥ , # 𝑍)
cong-exts σ≡σ′ rewrite σ≡σ′ = refl

cong-sub : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ} {T : Type} {t t′ : Δ ⊢ T}
         → σ ≡ σ′
         → t ≡ t′
         → t [ σ ] ≡ t′ [ σ′ ]
cong-sub σ≡σ′ t≡t′ rewrite σ≡σ′ | t≡t′ = refl

cong-sub-zero : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
              → t ≡ t′
              → _≡_ {A = Sub Γ (Γ , T)} (subst-id , t) (subst-id , t′)
cong-sub-zero t≡t′ rewrite t≡t′ = refl

cong-cons : ∀ {Γ Δ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {σ σ′ : Sub Γ Δ}
          → t ≡ t′
          → σ ≡ σ′
          → _≡_ {A = Sub Γ (Δ , T)} (σ , t) (σ′ , t′)
cong-cons t≡t′ σ≡σ′ rewrite t≡t′ | σ≡σ′ = refl

cong-seq : ∀ {Γ Δ Σ : Ctx} {τ τ′ : Sub Γ Δ} {σ σ′ : Sub Δ Σ}
         → σ ≡ σ′
         → τ ≡ τ′
         → σ ∘ τ ≡ σ′ ∘ τ′
cong-seq σ≡σ′ τ≡τ′ rewrite σ≡σ′ | τ≡τ′ = refl

≡-,-invertᵣ : ∀ {Γ Δ : Ctx} {T : Type} {ρ ρ′ : Ren Γ Δ} {x : Γ ∋ T}
            → _≡_ {A = Ren Γ (Δ , T)} (ρ , x) (ρ′ , x)
            → ρ ≡ ρ′
≡-,-invertᵣ refl = refl


-- Renaming a lookup judgement is equivalent to applying the
-- renaming to a variable with that lookup judgement
ren≡[x]ᵣ : ∀ {Γ Δ : Ctx} {T : Type} {x : Δ ∋ T} {ρ : Ren Γ Δ}
         → # (ren x ρ) ≡ # x [ ρ ]ᵣ
ren≡[x]ᵣ {x = 𝑍} {ρ , y} = refl
ren≡[x]ᵣ {x = 𝑆 x} {ρ , y} = ren≡[x]ᵣ {x = x} {ρ}

-- Applying a shifted renaming to a variable is equivalent
-- to incrementing the original renaming of the variable's
-- lookup judgemnet:
--   # x [ σ ↥ ] ≡ 𝑆 (rename x σ) (where σ is a renaming substitution)
shift-var : ∀ {Γ Δ : Ctx} {S T : Type} {x : Γ ∋ T} {ρ : Ren Δ Γ}
          → # x [ subst-ren (_↥ᵣ {T = S} ρ) ] ≡ # (𝑆 (ren x ρ))
shift-var {x = 𝑍} {_ , _} = refl
shift-var {x = 𝑆 x} {ρ , _} = shift-var {x = x} {ρ}

-- Specialized version of the previous lemma
shift-rename : ∀ {Γ Δ : Ctx} {S T : Type} {x : Γ ∋ T} {ρ : Ren Δ Γ}
             → ren x (_↥ᵣ {T = S} ρ) ≡ 𝑆 (ren x ρ)
shift-rename {x = 𝑍} {_ , _} = refl
shift-rename {x = 𝑆 x} {ρ , _} = shift-rename {x = x} {ρ}

-- Renaming with the identity renaming has no effect
rename-id : ∀ {Γ : Ctx} {T : Type} {x : Γ ∋ T}
          → ren x ren-id ≡ x
rename-id {x = 𝑍} = refl
rename-id {x = (𝑆_ {_} {S} x)}
  rewrite shift-rename {S = S} {x = x} {ρ = ren-id} | rename-id {x = x} = refl

-- Shifting is commutative between renaming/substitution: a shifted
-- renaming substitution is equivalent to a substitution created from
-- a shifted renaming
shift-rename-subst : ∀ {Γ Δ : Ctx} {T : Type} {ρ : Ren Γ Δ}
                   → subst-ren (_↥ᵣ {T = T} ρ) ≡ _↥ {T = T} (subst-ren ρ)
shift-rename-subst {ρ = ∅} = refl
shift-rename-subst {T = T} {ρ = _,_ {S = S} ρ x}
  rewrite shift-rename-subst {T = T} {ρ = ρ}
        | ≡-sym (ren≡[x]ᵣ {x = x} {ρ = _↥ᵣ {T = T} ren-id})
        | shift-rename {S = T} {x = x} {ρ = ren-id}
        | rename-id {x = x}                                 = refl

rename-subst-ren : ∀ {Γ Δ : Ctx} {T : Type} {ρ : Ren Γ Δ} {t : Δ ⊢ T}
                   → t [ ρ ]ᵣ ≡ t [ subst-ren ρ ]
rename-subst-ren {t = zero} = refl
rename-subst-ren {t = suc} = refl
rename-subst-ren {t = rec} = refl
rename-subst-ren {ρ = _ , _} {# 𝑍} = refl
rename-subst-ren {ρ = ρ , _} {# 𝑆 x}
  rewrite rename-subst-ren {ρ = ρ} {# x} = refl
rename-subst-ren {T = S ⇒ T} {ρ} {ƛ t}
  rewrite rename-subst-ren {ρ = ρ ↥ᵣ , 𝑍} {t}
        | shift-rename-subst {T = S} {ρ = ρ} = refl
rename-subst-ren {ρ = ρ} {r · s}
  rewrite rename-subst-ren {ρ = ρ} {r}
        | rename-subst-ren {ρ = ρ} {s} = refl

shift≡∘incr : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ} {T : Type}
             → σ ↥ ≡ σ ∘ subst-incr {T = T}
shift≡∘incr {σ = ∅}                                       = refl
shift≡∘incr {Γ} {σ = _,_ {S = S} σ s} {T}
  rewrite shift≡∘incr {σ = σ} {T = T}
        | rename-subst-ren {ρ = ren-incr {Γ} {T}} {t = s} = refl

ext-cons-shift : ∀ {Γ Δ : Ctx} {T : Type} {σ : Sub Γ Δ}
               → _≡_ {A = Sub (Γ , T) (Δ , T)} (σ ↥ , # 𝑍) (σ ∘ subst-incr , # 𝑍)
ext-cons-shift {σ = ∅}                               = refl
ext-cons-shift {Γ} {T = T} {σ , s}
  rewrite rename-subst-ren {ρ = ren-incr {Γ} {T}} {s}
        | shift≡∘incr {σ = σ} {T = T}                 = refl

ext-cons-Z-shift : ∀ {Γ Δ : Ctx} {ρ : Ren Γ Δ} {T : Type}
                → subst-ren (ρ ↥ᵣ , 𝑍) ≡ subst-ren ρ ∘ subst-incr , # 𝑍 {T = T}
ext-cons-Z-shift = cong-cons refl (≡-trans shift-rename-subst shift≡∘incr)

-- Lemma for expanding an identity substitution once
id≡id↑,x : ∀ {Γ : Ctx} {T : Type} → subst-id {Γ , T} ≡ (_↥ {T = T} subst-id , # 𝑍)
id≡id↑,x {∅} = refl
id≡id↑,x {Γ , T} {S}
  rewrite id≡id↑,x {Γ} {T}
        | shift-rename-subst {Γ , T} {Γ} {S} {ρ = ren-id ↥ᵣ} = refl

-- The identity substititon has no effect
-}
postulate
  [id]-identity : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
                → t [ id ] ≡ t
{-
[id]-identity {t = zero} = refl
[id]-identity {t = suc} = refl
[id]-identity {t = rec} = refl
[id]-identity {t = # 𝑍} = refl
[id]-identity {t = # (𝑆_ {_} {S} x)}
  rewrite shift-var {S = S} {x = x} {ρ = ren-id} | rename-id {x = x} = refl
[id]-identity {Γ} {T} {ƛ_ {S} t}
  rewrite ≡-sym (id≡id↑,x {Γ} {S}) | [id]-identity {t = t} = refl
[id]-identity {t = r · s}
  rewrite [id]-identity {t = r} | [id]-identity {t = s} = refl

-- sub-idR
id-compose-identity : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ}
                    → σ ∘ subst-id ≡ σ
id-compose-identity {σ = ∅} = refl
id-compose-identity {σ = σ , s}
  rewrite id-compose-identity {σ = σ} | [id]-identity {t = s} = refl

ren-ren≡ren∘ : ∀ {Γ Δ Σ : Ctx} {T : Type} {ω : Ren Γ Δ} {ρ : Ren Δ Σ}
                 {x : Σ ∋ T}
             → ren (ren x ρ) ω ≡ ren x (ρ ∘ᵣ ω)
ren-ren≡ren∘ {ρ = ρ , x} {x = 𝑍}       = refl
ren-ren≡ren∘ {ω = ω} {ρ , _} {x = 𝑆 x} = ren-ren≡ren∘ {ω = ω} {ρ} {x}

compose-ext : ∀ {Γ Δ Σ : Ctx} {ω : Ren Γ Δ} {ρ : Ren Δ Σ} {T : Type}
  → _≡_ {A = Ren (Γ , T) (Σ , T)} ((ρ ↥ᵣ , 𝑍) ∘ᵣ (ω ↥ᵣ , 𝑍)) ((ρ ∘ᵣ ω) ↥ᵣ , 𝑍)
compose-ext {ρ = ∅} = refl
compose-ext {ω = ω} {_,_ {S = S} ρ x} {T}
  rewrite ≡-,-invertᵣ (compose-ext {ω = ω} {ρ} {T})
        | shift-rename {S = T} {x = x} {ω}         = refl

compose-rename : ∀ {Γ Δ Σ : Ctx} {T : Type} {t : Σ ⊢ T} {ω : Ren Γ Δ}
                   {ρ : Ren Δ Σ}
               → t [ ρ ]ᵣ [ ω ]ᵣ ≡ t [ ρ ∘ᵣ ω ]ᵣ
compose-rename {t = zero} = refl
compose-rename {t = suc} = refl
compose-rename {t = rec} = refl
compose-rename {t = # x} {ω} {ρ} rewrite ren-ren≡ren∘ {ω = ω} {ρ} {x} = refl
compose-rename {t = ƛ_ {S = S} t} {ω} {ρ}
  rewrite compose-rename {t = t} {ω ↥ᵣ , 𝑍} {ρ ↥ᵣ , 𝑍}
        | compose-ext {ω = ω} {ρ} {S}                 = refl
compose-rename {t = r · s} {ω} {ρ}
  rewrite compose-rename {t = r} {ω} {ρ} | compose-rename {t = s} {ω} {ρ} = refl

-- TODO
postulate
  sub-tail : ∀ {Γ Δ : Ctx}  {T : Type} {t : Γ ⊢ T} {σ : Sub Γ Δ}
           → subst-incr ∘ (σ , t) ≡ σ

-- sub-idL
id-compose-identityˡ : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ}
                     → subst-id ∘ σ ≡ σ
id-compose-identityˡ {σ = ∅}                                  = refl
id-compose-identityˡ {σ = σ , t} rewrite sub-tail {t = t} {σ} = refl

sub-η : ∀ {Γ Δ : Ctx} {S T : Type} {σ : Sub Γ (Δ , S)}
      → (subst-incr ∘ σ  , # 𝑍 [ σ ]) ≡ σ
sub-η {σ = ∅ , x}                                                  = refl
sub-η {S = S} {σ = σ , r , s} rewrite sub-tail {T = S} {s} {σ , r} = refl
-}

-- TODO
postulate
  subst-compose : ∀ {Γ Δ Σ : Ctx} {T : Type} {τ : Sub Γ Δ} {σ : Sub Δ Σ}
                    {t : Σ ⊢ T}
                → t [ σ ] [ τ ] ≡ t [ σ ∘ τ ]

{-
subst-compose-↥ : ∀ {Γ Δ Σ : Ctx} {S : Type} {τ : Sub Γ Δ}
                    {σ : Sub Δ Σ} {s : Γ ⊢ S}
                → (σ ↥) ∘ (τ , s) ≡ σ ∘ τ
subst-compose-↥ {Σ = ∅} {σ = ∅} = refl
subst-compose-↥ {Δ = Δ} {Σ , T} {S} {τ} {σ , t} {s}
  rewrite subst-compose-↥ {τ = τ} {σ} {s}
        | rename-subst-ren {ρ = ren-incr {T = S}} {t}
        | subst-compose {τ = τ , s} {σ = subst-incr} {t}
        | sub-tail {t = s} {τ}                           = refl
-}
```
-->

### Soundness

To prove that the algorithm for normalization by evaluation implemented
preserves the meaning of a program (⟦ nf(t) ⟧ = ⟦ t ⟧, which we will just refer
to as soundness from now on), we will prove that a term is definitionally equal
to its normal form:

   Γ ⊢ t = nf(t) : T

In proving that a term is definitionally equal to its normal form, we will have
that `⟦ nf (t) ⟧ = ⟦ t ⟧`, as definitional equality implies semantic equality.
This new property we wish to prove expands to:

    Γ ⊢ t = ↓ᵀ a Γ, where a = ⟦ t ⟧ ↑Γ

To prove this, we will establish a logical relation `Γ ⊢ t : T Ⓡ a` between a
well-typed term `Γ ⊢ t : T` and a semantic object in our meta language
`a ∈ ⟦ T ⟧` such that it implies `Γ ⊢ t = ↓ᵀ a Γ : T`. Later, we will prove that
`Γ ⊢ t : T Ⓡ ⟦ t ⟧ ↑Γ` (finishing our proof) but we will focus on the logical
relation itself for now.

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
a lemma that has been omitted, `==-subst`, which postulates that if two terms
are definitionally equal, the terms with the same substitution applied are still
definitionally equal.

```agda
postulate
  ==-subst : ∀ {Γ Δ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {σ : Sub Δ Γ}
           → t == t′
           → t [ σ ] == t′ [ σ ]
```
<!---
```agda
{-
==-subst β-rec-z = trans β-rec-z refl
==-subst β-rec-s = trans β-rec-s refl
==-subst {t = (ƛ t) · s} {σ = σ} β-ƛ
  rewrite subst-compose {τ = σ} {σ = subst-id , s} {t = t}
        | id-compose-identityˡ {σ = σ} =
  trans
    β-ƛ
    (≡→==
      (≡-trans
        (subst-compose {t = t})
        (cong-sub {t = t}
          (cong-cons
            refl
            (≡-trans
              subst-compose-↥
              id-compose-identity))
          refl)))
==-subst {T = S ⇒ T} {t} {σ = σ} η
  rewrite subst-compose {τ = _↥ {T = S} σ , # 𝑍} {subst-incr} {t}
        | sub-tail {t = # 𝑍 {T = S}} {σ ↥}                        =
    trans η (≡→== lemma)
  where
    lemma : ƛ t [ σ ] [ subst-incr ] · # 𝑍 ≡ ƛ t [ σ ↥ ] · # 𝑍
    lemma rewrite subst-compose {τ = subst-incr {T = S}} {σ} {t}
                | shift≡∘incr {σ = σ} {T = S}                    = refl
==-subst (abs-compatible t==t′) = abs-compatible (==-subst t==t′)
==-subst (app-compatible r==s r′==s′) =
  app-compatible (==-subst r==s) (==-subst r′==s′)
==-subst refl = refl
==-subst (sym t==t′) = sym (==-subst t==t′)
==-subst (trans t₁==t₂ t₂==t₃) = trans (==-subst t₁==t₂) (==-subst t₂==t₃)
-}
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
  ==⟨ sym (==-subst t==t′) ⟩
    Γ′≤Γ ≤⊢ t
  ==⟨ pf Γ′≤Γ ⟩
    unit
  ==∎
==-Ⓡ-trans {T = 𝟙} {t} {t′} {ne 𝓊̂} t==t′ pf {Γ′} Γ′≤Γ
  with 𝓊̂ Γ′          | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩ | t==𝓊 =
  begin==
    Γ′≤Γ ≤⊢ t′
  ==⟨ sym (==-subst t==t′) ⟩
    Γ′≤Γ ≤⊢ t
  ==⟨ t==𝓊 ⟩
    𝓊
  ==∎
==-Ⓡ-trans {T = S ⇒ T} {r} {r′} r==r′ pf Γ′≤Γ sⓇa =
  ==-Ⓡ-trans r·s==r′·s r·sⓇfa
  where
    r·s==r′·s = app-compatible (==-subst r==r′) refl
    r·sⓇfa = pf Γ′≤Γ sⓇa
```

Additionally, because we have defined the relation so that its implication holds
for all extensions of a context, we can "weaken" the logical relation
`Γ ⊢ t : T Ⓡ a` for all `Γ′ ≤ Γ`, having that `Γ′ ⊢ t : T Ⓡ a` holds as well.
For this proof, we use another postulated lemma that weakening a term `t` twice
is equivalent to weakening it once with a composed weakening substitution.

<!---
```agda
-- TODO
```
--->
```agda
postulate
  weaken-compose : ∀ {Σ Δ Γ : Ctx} {T : Type}
    → (Σ≤Δ : Σ ≤ Δ)
    → (Δ≤Γ : Δ ≤ Γ)
    → (t : Γ ⊢ T)
    → Σ≤Δ ≤⊢ Δ≤Γ ≤⊢ t ≡ (≤-trans Σ≤Δ Δ≤Γ) ≤⊢ t

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

The first lemma is:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : T) ⇒ Γ ⊢ 𝓊 : T Ⓡ ↑ᵀ 𝓊̂

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

The second lemma we need is:

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


    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : S → T) ⇒ Γ ⊢ 𝓊 : S → T Ⓡ ↑ˢ⃗ᵗ 𝓊̂

By definition of `Ⓡ`, this expands to:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : S → T) ⇒
      ∀ Γ′ ≤ Γ. Γ′ ⊢ s Ⓡ a ⇒
        Γ′ ⊢ 𝓊 s Ⓡ (↑ˢ⃗ᵗ 𝓊̂) a

This simplifies further by the definition of reflection:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : S → T) ⇒
      ∀ Γ′ ≤ Γ. Γ′ ⊢ s Ⓡ a ⇒
        Γ′ ⊢ 𝓊 s Ⓡ ↑ᵀ (𝓊̂ · ↓ˢ a)

Our induction hypothesis gives us that at type `T`, the following holds:

    (∀ Γ″ ≤ Γ′. Γ″ ⊢ 𝓊 s = (𝓊̂ · ↓ˢ a) Γ″) ⇒
        Γ′ ⊢ 𝓊 s Ⓡ ↑ᵀ (𝓊̂ · ↓ˢ a)

With our induction hypothesis, our new goal is to prove only that:

    Γ″ ⊢ 𝓊 s = (𝓊̂ · (↓ˢ a)) Γ″ : T

for any `Γ″` that is an extension of `Γ′` (which itself extends `Γ`). Note that
`(𝓊̂ · (↓ˢ a)) Γ″` is equivalent to `𝓊̂(Γ″) · (↓ˢ a)(Γ″)` (application of liftable
neutrals is overloaded), so the final form of the property we have to prove is:

    Γ″ ⊢ 𝓊 s = 𝓊̂(Γ″) · ↓ˢ a Γ″ : T

Using the definitional equality rule of compatibility for application, we need
only prove that:

    Γ″ ⊢ 𝓊 = 𝓊̂(Γ″) : S → T
    Γ″ ⊢ s = ↓ˢ a Γ″ : S

The first property is our given evidence, and the second property follows from
the second lemma we will be proving:

    Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ′ : T

We have that `Γ′ ⊢ s : S Ⓡ a`, so we can apply this lemma to arrive at the
second property we need. The proof in Agda is as described above:

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
        ==⟨ app-compatible (≡→== (weaken-compose Γ″≤Γ′ Γ′≤Γ 𝓊)) refl ⟩
          (Γ″≤Γ ≤⊢ 𝓊) · (Γ″≤Γ′ ≤⊢ s)
        ==⟨ app-compatible 𝓊==𝓊″ refl ⟩
          𝓊″ · (Γ″≤Γ′ ≤⊢ s)
        ==⟨ app-compatible refl s==↓ᵀaΓ″ ⟩
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
`unit` or an embedded liftable neutral `𝓊̂`.

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
      ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ˢ⃗ᵗ f Γ′

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
      ==⟨ app-compatible subst-lemma refl ⟩
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
      ≡→== (≡-trans
             (subst-compose {τ = ↥} {weaken Γ′≤Γ} {t})
             (≡-sym [id]-identity))
```

Lastly, we can quickly derive the lemma `Γ , x:T ⊢ x : T Ⓡ ↑ᵀ 𝓍̂ Γ` used in the
previous lemma using `(∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ′) : T) ⇒ Γ ⊢ 𝓊 Ⓡ ↑ᵀ 𝓊̂`. Again, we
use a lemma we have left out in the rendering ─ that any proof of context
extension is equivalent.

```agda
xⓇ↑ᵀ𝓍̂ {_} {T} = ==^→Ⓡ↑ x==𝓍̂ where
  x==𝓍̂ : ∀ {Γ Γ′ : Ctx}
       → (Γ′≤Γ,T : Γ′ ≤ (Γ , T))
       → Γ′≤Γ,T ≤⊢ # 𝑍 ==^ 𝓍̂ T Γ
  x==𝓍̂ {Γ} {Γ′} pf
    with Γ′ ≤? (Γ , T)
  ... | no ¬pf         = ¬pf pf
  ... | yes pf′
    with 𝓍̂ T Γ | ≤-pf-irrelevance pf pf′
  ... | _      | refl
    with weakenᵣ pf′ 𝑍
  ...| _               = refl
```

Let's focus on one of the lemmas we have proven:

    Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ : T

We have defined our logical relation with the property that this lemma gives us
that:
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
environment `ε`.

```agda
_Ⓡˢ_ : ∀ {Γ Δ : Ctx} → Sub Γ Δ → ⟦ Δ ⟧ → Set
_Ⓡˢ_ {Δ = Δ} σ ε = ∀ {T : Type} → (x : Δ ∋ T) → σ x Ⓡ env-lookup x ε
```

<!---
```agda
infix 4 _Ⓡˢ_
```
--->

Similarly as for logical relations between terms and semantic objects, if a
logical relation holds between a substitution and an environment, it holds for
any weakening of the substitution. The proof is immediate using `Ⓡ-weaken`.

```agda
Ⓡˢ-weaken : ∀ {Γ′ Γ Δ : Ctx} {Γ′≤Γ : Γ′ ≤ Γ} {σ : Sub Γ Δ} {ε : ⟦ Δ ⟧}
           → σ Ⓡˢ ε
           → σ ∘ (weaken Γ′≤Γ) Ⓡˢ ε
Ⓡˢ-weaken {Γ′≤Γ = Γ′≤Γ} σⓇε x = Ⓡ-weaken {Γ′≤Γ = Γ′≤Γ} (σⓇε x)
```

These two lemmas will be necessary for our proofs, which we are now ready to
begin laying out. We introduce the semantic typing judgement `Γ ⊨ t : T`:

```agda
_⊨_ : ∀ {T : Type} → (Γ : Ctx) → Γ ⊢ T → Set
_⊨_ {T} Γ t =
  ∀ {Δ : Ctx} {σ : Sub Δ Γ} {ε : ⟦ Γ ⟧}
  → σ Ⓡˢ ε
    -------
  → t [ σ ] Ⓡ ⟦⊢ t ⟧ ε
```

That is, `Γ ⊨ t : T` is a judgement implying that if a substitution is logically
related to an environment, then the application of that substitution to a term
is logically related to the evaluation of that term under the environment. By
induction on the typing judgement `Γ ⊢ t : T`, we can prove the semantic typing
judgement `Γ ⊨ t : T`. This is called the fundamental lemma of logical
relations. For `zero` and `suc`, the cases follow immediately from how we have
defined the logical relation between terms and semantic objects. For `rec`, we
can use our earlier lemma. In the case of variables, the proof is essentially a
lookup into the environment for the semantic object that the variable is
logically related to, using our proof that `Γ ⊢ σ : Δ Ⓡ ε`). Application follows
from our inductive hypotheses, leaving us at the abstraction case, which is the
most complicated to prove.

In the case of an abstraction `Γ ⊢ λx. t : S → T`, we want to prove:
    Γ ⊢ σ : Δ Ⓡ ε ⇒
      Γ ⊢ (λx. t) [ σ ] : S → T Ⓡ ⟦ Γ ⊢ λx. t : S → T ⟧ ε

By the definition of the application of a substitution to an abstraction, as
well as the definition of evaluation of an abstraction, this simplifies to:

    Γ ⊢ σ : Δ Ⓡ ε ⇒
      Γ ⊢ λx. t [ σ ↥ , x / x ] : S → T Ⓡ f
        (where f = λ a → ⟦ Γ , x: S ⊢ t : T ⟧ (ε , a))

We can also expand this using the definition of `Ⓡ` for functions (and
immediately reducing the application of `f` to `a`):

    Γ ⊢ σ : Δ Ⓡ ε ⇒
      ∀ Γ′ ≤ Γ. Γ′ ⊢ s : S Ⓡ a ⇒
        Γ′ ⊢ (λx. t [ σ ↥ , x / x ]) · s : T Ⓡ ⟦ Γ , x:S ⊢ t : T ⟧ (ε , a)

Already, this is a tricky property to parse. To start, we can use our lemma
that `Ⓡ` is transitive with respect to definitional equality, and use the `β-ƛ`
rule to reduce `(λx. t [ σ ↑ , x/x ]) · s` to `t [ σ ↑ , x / x ] [s / x]`. Now,
we need only prove:

    Γ′ , x:S ⊢ t [ σ ↥ , x / x ] [ s / x ] : T Ⓡ ⟦ Γ , x:S ⊢ t : T ⟧ (ε , a)

Here, we can use a substitution lemma to reduce these two substitutions, giving
us:

    Γ′ , x:S ⊢ t [ σ ↥ , s / x ] : T Ⓡ ⟦ Γ , x:S ⊢ t : T ⟧ (ε , a)

Now, the property we want to show actually looks like our induction hypothesis.
With it, we have that we only need to show that:

     Γ′ , x:S ⊢ (σ ↥ , s / x) : Δ Ⓡ (ε , a)

This expands to proving both:

     Γ′ , x:S ⊢ σ ↥ : Δ Ⓡ ε
     Γ′ ⊢ s : S Ⓡ a

The first follows from our earlier lemma that if a substitution is logically
related to an environment, then so is a shifting of the substitution. The
second property follows from our given proof. With that, our abstraction case is
proven. In reality, there are a few other substitution lemmas that our
formalization forces us to use, but they are mostly irrelevant to the proofs
themselves at a high-level, having again to do mostly with the weakening
substitutions applied at the switching of contexts. [^1]

```agda
fundamental-lemma : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
                  → Γ ⊨ t
fundamental-lemma {t = unit} σⓇˢε _ = refl
fundamental-lemma {t = # x} σⓇˢε = σⓇˢε x
fundamental-lemma {t = ƛ t} {σ = σ} {ε} σⓇˢε Γ′≤Γ {s} {a} sⓇa =
  ==-Ⓡ-trans (sym β-ƛ) t[exts-σ][s]₀Ⓡ⟦t⟧⟨ε,a⟩
  where
    subst-lemma₁ =
      subst-compose {τ = sub-zero s} {exts (weaken Γ′≤Γ)} {t [ exts σ ]}
    subst-lemma₂ =
     subst-compose {τ = exts (weaken Γ′≤Γ) ∘ sub-zero s} {exts σ} {t}

    t[exts-σ] = t [ exts σ ] [ exts (weaken Γ′≤Γ) ]

    σ′ = exts σ ∘ exts (weaken Γ′≤Γ) ∘ sub-zero s

    σ′Ⓡ⟨ε,a⟩ : σ′  Ⓡˢ ⟨ ε , a ⟩
    σ′Ⓡ⟨ε,a⟩ 𝑍 = sⓇa
    σ′Ⓡ⟨ε,a⟩ (𝑆 x) = {!!}
    -- σ′ (𝑆 x)
    -- ↥ ∘ σ′ [ ren-shift (?) ]
    -- ↥ ∘ exts σ ∘ exts (weaken Γ′≤Γ) ∘ sub-zero s
    -- ↥ ∘ exts σ ∘ (s • weaken Γ′≤Γ) [ subst-zero-ext-cons ]
    -- ↥ ∘ (# 𝑍 • σ ∘ ↥) ∘ (s • weaken Γ′≤Γ) [ exts-cons-shit ]
    -- (↥ ∘ (# 𝑍 • σ ∘ ↥)) ∘ (s • weaken Γ′≤Γ)  [ sub-assoc ]
    -- (σ ∘ ↥) ∘ (s • weaken Γ′≤Γ) [ sub-tail ]
    -- σ ∘ (↥ ∘ (s • weaken Γ′≤Γ)) [ sub-assoc ]
    -- σ ∘ weaken Γ′≤Γ [ sub-tail ]

    -- Ⓡˢ-weaken {Γ′≤Γ = Γ′≤Γ} σⓇε

    t[exts-σ][s]₀Ⓡ⟦t⟧⟨ε,a⟩ : t[exts-σ] [ s ]₀ Ⓡ ⟦⊢ t ⟧ ⟨ ε , a ⟩
    t[exts-σ][s]₀Ⓡ⟦t⟧⟨ε,a⟩ rewrite subst-lemma₁ | subst-lemma₂ =
        fundamental-lemma {t = t} σ′Ⓡ⟨ε,a⟩
fundamental-lemma {t = r · s} {σ = σ} σⓇˢε
  with fundamental-lemma {t = r} σⓇˢε | fundamental-lemma {t = s} σⓇˢε
... | Γ⊨r                              | Γ⊨s
  with Γ⊨r ≤-id Γ⊨s
... | pf
  rewrite [id]-identity {t = r [ σ ]} = pf
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

Now, we arrive at the soundness of our algorithm for normalization by
evaluation. We have `Γ ⊢ id : Γ Ⓡ ↑Γ`, and using the fundamental lemma with
the identity substitution gives us:

    Γ ⊢ t [ id ] Ⓡ ⟦ t ⟧ ↑Γ

Note also that `t [ id ] ≡ t`. Using the lemma that logical relation between a
term and a semantic object implies the definitional equality of the term to the
reification of the semantic object, we have:

    Γ ⊢ t = ↓ᵀ (⟦ t ⟧ ↑Γ) Γ : T

Thus, our algorithm for normalization by evaluation is sound and preserves the
meaning of a term that it normalizes.

```agda
soundness : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
          → t == nf t
soundness {Γ} {T} {t}
  with fundamental-lemma {t = t} (idⓇ↑Γ {Γ})
... | tⓇ⟦t⟧↑Γ
  with Ⓡ→==↓ tⓇ⟦t⟧↑Γ ≤-id
... | t==↓ᵀ⟦t⟧↑Γ
  rewrite [id]-identity {t = t [ id ]}
        | [id]-identity {t = t}              = t==↓ᵀ⟦t⟧↑Γ

```

### Conclusion

In the end, we have formalized an algorithm in Agda for normalization by
evaluation that is based on the intuition of leaving the parts of a term that
cannot be evaluated (i.e. "unknowns") unchanged while still evaluating the parts
of the term that we do know how to reduce. The algorithm is both complete and
sound with respect to definitional equality, as we have proven. Completeness
followed quickly from the definition of the algorithm, while soundness required
a more in-depth proof involving the use of logical relations and the fundamental
lemma of logical relations.

In his habilitation thesis, Andreas Abel goes on to introduce the algorithm for
the untyped lambda calculus, from which he continues to build upon, arriving at
an algorithm for a language with dependent types and a language with
impredicativity. This introduction to normalization to evaluation should
hopefully be a good starting point to explore these and other extensions of the
algorithm, such as simply trying out these proofs for yourself with a different
extension of the simply typed lambda calculus, or implementing the algorithm
in a language other than Agda.

#### Unicode

This site uses the following unicode[^2]:

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
    ⁿ  U+207F  SUPERSCRIPT LATIN SMALL LETTER N (\^n)
    ᵃ  U+1D43  MODIFIER LETTER SMALL A (\^a)
    ᵗ  U+1D57  MODIFIER LETTER SMALL T (\^t)
    ˢ  U+02E2  MODIFIER LETTER SMALL S (\^s)
    ⃗  U+20D7  COMBINING RIGHT ARROW ABOVE (\^r)
    ↓  U+2193  DOWNWARDS ARROW (\d)
    ᶜ  U+1D9C  MODIFIER LETTER SMALL C (\^c)
    ˣ  U+02E3  MODIFIER LETTER SMALL X (\^x)
    ̂  U+0302  COMBINING CIRCUMFLEX ACCENT (\^)
    ℕ  U+2115  DOUBLE STRUCK CAPITAL N (\bN)
    𝓍  U+1D4CD  MATHEMATICAL SCRIPT SMALL X (\Mcx)
    ≰  U+2270  NEITHER LESS THAN NOR EQUAL TO (\len)
    ₃  U+2083  SUBSCRIPT 3 (\_3)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
    Ⓝ  U+24C3  CIRCLED LATIN CAPITAL LETTER N (\(n)2)
    Ⓡ  U+24C7  CIRCLED LATIN CAPITAL LETTER R (\(r)2)
    ″  U+2033  DOUBLE PRIME (\'2)
    ‴  U+2034  TRIPLE PRIME (\'3)
    ⁗  U+2057  QUADRUPLE PRIME (\'4)

#### References

[^1]: Note that there is a subtle detail here left out, we are implicitly
considering a substitution using `Γ′` but the original substitution is
`Γ ⊢ σ : Δ`. This gets a little too into the details of our substitutions, but
we are writing out `σ ↥` when really we should write out
`(σ ∘ weaken Γ′ ≤ Γ) ↥`. In the end, our reasoning still follows because the
composition of a weakening onto a substitution is really equivalent to shifting
it by that many extensions, and again ─ shifts do not affect the logical
relation between a substitution and an environment.

[^2]: ̂ (`\^`) may be displayed on top of another character when written after it (e.g. `\Mcu\^` produces 𝓊̂)
