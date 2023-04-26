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
Cockx. For clarity and readability, some parts of the source file are left out
in this rendering, and this will be called out when possible. At the moment,
some lemmas are included only as postulates. Some familiarity with
Agda (e.g. such as having worked through the first part of [Programming
Languages Foundations in Agda](https://plfa.inf.ed.ac.uk/22.08/)) is assumed
along with some knowledge of programming language foundations, though the content
is mostly self contained.

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

### System T

Before going into the algorithm itself, we will embed the language for which
we will be defining the algorithm: System T. System T is a small language with
natural numbers, higher-order functions, and primitive recursion.

<!---
### Imports

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
--->

We start off with the types of the language: natural numbers and functions.

```agda
data Type : Set where
  nat : Type
  _⇒_ : ∀ (S T : Type) → Type

infixr 7 _⇒_
```

<!---
```agda
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
--->

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

As for terms, System T has the variables, abstractions, and
application just like the lambda calculus. It has the constants
`zero` and `suc` (as a curried constant) for constructing naturals,
as well as `rec`, a curried constant for primitive recursion. The
following program increments the number 1 twice:

    (λx. suc (suc x)) (suc zero)

Terms in System T will be defined in our Agda formalization using
an *intrinsically* typed representation. We have defined our types
first, and terms are only every considered with respect to their type.

Using this representation, we only have to consider well-typed
terms. An Agda term `t` of type `Γ ⊢ T` is the well-typed System T
term `Γ ⊢ t : T` itself.

For clarity, when talking about terms we will not use their intrinsically
typed representation using de Brujin indices, though we will only consider
well-typed terms going forward. (e.g. the variable # 𝑍 will be referred to
as `Γ , x:T ⊢ x : T`)

```agda
data _⊢_ (Γ : Ctx) : Type → Set where
  zero : Γ ⊢ nat

  suc : Γ ⊢ nat ⇒ nat

  rec  : ∀ {T : Type}
         ---------------------------------
       → Γ ⊢ (T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T)

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

We can define some sample programs in the language
using these constructors:

```agda
-- Γ ⊢ λx. x : T → T
ex0 : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T ⇒ T
ex0 = ƛ # 𝑍

-- ∅ ⊢ (λx. x) zero : nat
ex1 : ∅ ⊢ nat
ex1 = ex0 · zero

-- ∅ ⊢ suc ((λx. x) zero) : nat
ex2 : ∅ ⊢ nat
ex2 = suc · ex1

-- ∅ , x:nat, y:nat ⊢ suc ((λz. suc y) x) : nat
ex3 : ∅ , nat , nat ⊢ nat
ex3 = suc · ((ƛ suc · # 𝑆 𝑍) · # 𝑆 𝑍)
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

It will be helpful to make this relation decidable, for which we define
an infix function `≤?`. Note that to define it we use another function
whose definition has been omitted for brevity:

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

Interestingly, because of how we've defined our relation, the typical "obvious"
case for a sublist relationship, that the empty list is a sublist of any other
list, has to be proven separately as a lemma.

```agda
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

Now that we have defined System T in Agda, we are almost ready
to start describing an algorithm for normalization by
evaluation. However, to prove properties concerning this algorithm,
we will need to define two more language constructs: substitutions
and equality.

### Substitution

A parallel substitution `Γ ⊢ σ : Δ` in System T provides
a term in `Γ` to substitute for each variable in the context
`Δ` -- `Γ ⊢ σ : Δ` can be read as "σ is a substitution for the
context `Δ` using `Γ`". It is defined with the following two
rules:

                            Γ ⊢ σ : Δ       Γ ⊢ t : S
    ----------             --------------------------
    Γ ⊢ ∅ : ∅              Γ ⊢ (σ , x / s) : Δ , x:S

That is, any context can be used to substitute for the empty context (an "empty"
substitution), and any substitution can be extended with a well-typed term in
the substitution's "source" context. In Agda, the rules are:

```agda
data Sub : Ctx → Ctx → Set where
  ∅ : ∀ {Γ} → Sub Γ ∅

  _,_ : ∀ {Γ Δ : Ctx} {S : Type}
        → Sub Γ Δ
        → Γ ⊢ S
          ---------
        → Sub Γ (Δ , S)
```

This substition can be used to actually substitute a variable
for a term -- an operation that is simply a "lookup" in the
"list" of terms that makes up a parallel substitution.

```agda
sub : ∀ {Γ Δ : Ctx} {S : Type}
    → Δ ∋ S
    → Sub Γ Δ
      -------
    → Γ ⊢ S
sub 𝑍     (_ , s) = s
sub (𝑆 x) (σ , _) = sub x σ
```

We also wish to actually use this substitution, which is why we
will define an operation for the application of a substitution
to a term:


    Δ ⊢ σ : Γ      Δ ⊢ t : T
    ------------------------
         Γ ⊢ t [ σ ] : T

Given a substitution σ for `Δ` using `Γ`, we can transform a term `t`
that is well-typed in the context `Δ` to a term `t [ σ ]` that is
well typed in the context `Γ`

Defining this operation is actually a little tricky in Agda, because
the language requires all code that is written to be terminating.
The typical definition of the application of a substitution `σ` is not
obviously terminating, so we will need to first introduce renaming.

Renaming is a specialized substitution where we can only substitute variables
with other variables (i.e. a renaming `Γ ⊢ σᵣ : Δ` provides a variable in `Γ`,
not a term in `Γ`, to replace for every variable in `Δ`).

It is necessary to first to define renaming substitutions so that termination
is guaranteed. In general, when referring to a renaming substitution (or a
related operation), we will use the subscript 'ᵣ'.

```agda
data Ren : Ctx → Ctx → Set where
  ∅ : ∀ {Γ : Ctx} → Ren Γ ∅

  _,_ : ∀ {Γ Δ : Ctx} {S : Type}
      → Ren Γ Δ
      → Γ ∋ S
        -------------
      → Ren Γ (Δ , S)
```

Since a renaming is really just a specialized substitution,
we can transform any renaming substitution into a parallel
substitution.

```agda
subst-ren : ∀ {Γ Δ : Ctx} → Ren Γ Δ → Sub Γ Δ
subst-ren ∅ = ∅
subst-ren (σᵣ , x) = subst-ren σᵣ , # x
```

However, because renaming substitutions are specialized to
variables, we can use them to rename variables (i.e. convert between lookup
judgements), an operation that is similar to `sub`.

```agda
ren : ∀ {Γ Δ : Ctx} {S : Type}
    → Δ ∋ S
    → Ren Γ Δ
      -------
    → Γ ∋ S
ren 𝑍     (ρ , x) = x
ren (𝑆 x) (ρ , _) = ren x ρ
```

You may have seen renamings before as simply a type synonym
for the Agda type `∀ {T} → Γ ∋ T → Δ ∋ T` (or similar) -- that is,
the renaming is itself the mapping that we have defined above. Our
definition makes the distinction here of having renamings defined
separately because it allows us to easily define a shifting operation
over them (and the same reasoning applies to substitutions).

```agda
_↥ᵣ : ∀ {Γ Δ : Ctx} {T : Type}
    → Ren Γ Δ
      -------------
    → Ren (Γ , T) Δ
∅ ↥ᵣ       = ∅
(σᵣ , x) ↥ᵣ = σᵣ ↥ᵣ , 𝑆 x

infix 6 _↥ᵣ
```

Shifting a renaming substitution shifts all indices in the renaming by
one -- in other words, given a renaming for `Δ` using `Γ`, we can create
a renaming for `Δ` using `Γ , x:T`. If we had represented renamings simply
as `∀ {T} → Γ ∋ T → Δ ∋ T`, this operation would be impossible to define.

    impossible : ∀ {Γ Δ : Ctx} {S : Type}
               → (∀ {T : Type} → Γ ∋ T → Δ ∋ T)
               → (∀ {T : Type} → Γ , S ∋ T → Δ ∋ T)
    impossible σᵣ 𝑍     = ?    -- Here, there is no lookup judgement we can use
    impossible σᵣ (𝑆 x) = σᵣ x

We will use the shifting renaming to extend renaming under a binder,
but more importantly we will need this operation because context extensions
are a core part of the algorithm for normalization by evaluation we will define
is context extensions. With this operation, we can define a renaming for a
context `Γ` using a `Γ′` such that `Γ′ ≤ Γ`. This renaming is really a series
of shifts based on how many extensions to `Γ` the context `Γ′` contains.

Its definition depends on one more key renaming, the identity renaming. The
identity renaming just renames each variable with itself. We define it mutually
with an "increment" renaming (a special case of the shifting renaming), which
will be useful later on.

```agda
mutual
  ren-id : ∀ {Γ : Ctx} → Ren Γ Γ
  ren-id {∅} = ∅
  ren-id {Γ , T} = ren-incr , 𝑍

  ren-incr : ∀ {Γ : Ctx} {T : Type} → Ren (Γ , T) Γ
  ren-incr = ren-id ↥ᵣ
```

Using these, we can define a renaming for a context `Γ` using any of its
extensions.

```
ren-≤ : ∀ {Γ′ Γ : Ctx} → Γ′ ≤ Γ → Ren Γ′ Γ
ren-≤ ≤-id = ren-id
ren-≤ (≤-ext pf) = (ren-≤ pf) ↥ᵣ
```

The application of a renaming substituion `Γ ⊢ σᵣ : Δ` to a term `Δ ⊢ t : T`
rebases the term to the context `Γ`. This is done by "distributing" the
renaming substitution across all subterms of the term, renaming all variables
used in the term with their corresponding variable in `Γ`.

```agda
_[_]ᵣ : ∀ {Γ Δ : Ctx} {T : Type}
        → Δ ⊢ T
        → Ren Γ Δ
          -------
        → Γ ⊢ T
zero [ _ ]ᵣ = zero
suc [ _ ]ᵣ = suc
rec [ _ ]ᵣ = rec
# x [ σᵣ ]ᵣ = # ren x σᵣ
(ƛ t) [ σᵣ ]ᵣ = ƛ t [ σᵣ ↥ᵣ , 𝑍 ]ᵣ
(r · s) [ σᵣ ]ᵣ = r [ σᵣ ]ᵣ · s [ σᵣ ]ᵣ

infix 8 _[_]ᵣ
```

Renaming substitutions now allow us to build out parallel
substitutions and their operations such that these operations
are guaranteed to terminate. As was done for renaming substitutions, we define a
shifting operation for parallel substitutions, to be used for extending a
substitution under a binder.

```agda
_↥ : ∀ {Γ Δ : Ctx} {T : Type}
      → Sub Γ Δ
        -------------
      → Sub (Γ , T) Δ
∅ ↥       = ∅
(σ , s) ↥ = σ ↥ , s [ ren-incr ]ᵣ
```

<!---
```
infix 6 _↥
```
--->

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
zero [ _ ] = zero
suc [ _ ] = suc
rec [ _ ] = rec
# x [ σ ] = sub x σ
(ƛ t) [ σ ] = ƛ (t [ σ ↥ , # 𝑍 ])
(r · s) [ σ ] = r [ σ ] · s [ σ ]
```

<!---
```
infix 8 _[_]
```
--->

Substitutions can be composed by applying a substitution `Γ₁ ⊢ τ : Γ₂`
to every term in a substitution `Γ₂ ⊢ σ : Γ₃`. This will be useful
for a few substitution lemmas we will use in our proofs.

```agda
_∘_ : ∀ {Γ₁ Γ₂ Γ₃ : Ctx} → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₂ → Sub Γ₁ Γ₃
∅       ∘ _ = ∅
(σ , s) ∘ τ = (σ ∘ τ) , s [ τ ]
```

A well-typed term in `Γ` can be "weakened" to a well-typed term in a context
`Γ′` by using a weakening substitution. Really, this substitution is the
renaming substitution between extended contexts. We will use `_≤⊢_` as a
a shorthand for applying a weakening substitution (and in Agda, this will
look a lot like an extended judgement: `Γ′≤Γ ≤⊢ t`).

```agda
weaken : ∀ {Γ′ Γ : Ctx}
       → Γ′ ≤ Γ
         --------
       → Sub Γ′ Γ
weaken pf = subst-ren (ren-≤ pf)

_≤⊢_ : ∀ {Γ′ Γ : Ctx} {T : Type} → Γ′ ≤ Γ → Γ ⊢ T → Γ′ ⊢ T
pf ≤⊢ t = t [ weaken pf ]
```

<!---
```agda
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
undecidable. Instead, we will want to use βη-equivalence. In STLC, we have
that two terms are βη-equivalent iff they have the same meaning. The same
applies for System T (which is really a version of STLC with primitive
recursion), so by extending βη-equivalence to System T so we can actually prove
the last property. Specifically, we will prove that `Γ ⊢ nf(t) = t : T`, a
notation used to indicate that the two terms are _definitionally equal_ ─ the
extension to βη-equivalence that we will be defining and using.

To do so, we will need to actually define operations for β-reductions and
η-expansions. For this, we will first define two parallel substitutions: the
identity and incrementing substitutions. These will be used to establish
β- and η-equivalence, respectively. For the incrementing substitution, we
will benefit from a shorthand as we did for the weakening substitution.

```agda
subst-id : ∀ {Γ : Ctx} → Sub Γ Γ
subst-id = subst-ren ren-id

subst-incr : ∀ {Γ : Ctx} {T : Type} → Sub (Γ , T) Γ
subst-incr = subst-ren ren-incr

_↑⊢_ : ∀ {Γ : Ctx} {T : Type} → (S : Type) → Γ ⊢ T → Γ , S ⊢ T
_ ↑⊢ t = t [ subst-incr ]
```

<!---
```
infixr 5 _↑⊢_
```
--->

A β-reduction will be the application `t [ id , s / x ]` of the identity
substitution extended with the term `s` that we are substituting for a
variable `x` in a term `Γ , x:S ⊢ t : T`. We will use the shorthand
`t [ s / x ]` to refer to the application of this substitution.

```agda
_[_/x] : ∀ {Γ : Ctx} {S T : Type}
  → Γ , T ⊢ S
  → Γ ⊢ T
    ---------
  → Γ ⊢ S
s [ t /x] =  s [ subst-id , t ]
```

<!---
```
infix 8 _[_/x]
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
η-expand t = ƛ t [ subst-incr ] · # 𝑍
```

With these defined, we can actually introduce definitional equality in Agda.
The relation is an extension of βη-equivalence for the simply-typed lambda
calculus that includes the computation rules for the primitive recursion
operation that differentiates System T from STLC. We use `t == t′` in Agda
instead of `Γ ⊢ t = t′ : T`, though we will refer to two terms that are
definitionally equal with the latter.

```agda
data _==_ : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → Γ ⊢ T → Set where

  -- Computation rules, i.e. β-reductions
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
reasoning for propositional equality.

<!---
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
```
--->

```agda
open ==-Reasoning public
```

### Evaluation

The evaluation, or interpretation, `⟦ t ⟧` of a well-typed term `Γ ⊢ t : T`
assigns a meaning to `t` by equating it to a semantic object in our meta
language, using an interpretation of the context `Γ` (an _environment_)
under which the term `t` is well-typed.

For types, we can interpret naturals in System T as ℕ, and functions in
System T as Agda functions, defined inductively on their types.

    ⟦ nat ⟧ = ℕ
    ⟦ S ⇒ T ⟧ = ⟦ S ⟧ → ⟦ T ⟧

An empty context is interpreted as the unit type (an empty environment), and an
extension to a context is defined inductively, with the extension itself being
the interpretation of the type the context is extended with.

    ⟦ ∅ ⟧ = ⊤
    ⟦ Γ , S ⟧ = ⟦ Γ ⟧ × ⟦ S ⟧

From now on, we will use the metavariable ρ to represent environments. The
interpretation of a variable expects an environment, and is essentially a
lookup into the environment for the variable's value:

    ⟦ Γ ∋ x:T ⟧ (ρ ∈ ⟦ Γ ⟧) ∈ ⟦ T ⟧
    ⟦ Γ , T ∋ x:T ⟧ (ρ , a) = a
    ⟦ Γ , y:S ∋ x:T ⟧ (ρ , _) = ⟦ Γ ∋ x:T ⟧ ρ

The interpretation of a typed term expects an environment as well. We only
include the evaluation rules for variables, abstractions, and application.

    ⟦ Γ ⊢ t : T ⟧ (ρ ∈ ⟦Γ⟧) = ⟦ T ⟧
    ⟦ Γ ⊢ x : T ⟧ ρ = ⟦ Γ ∋ x:T ⟧ ρ
    ⟦ Γ ⊢ λx . t : S ⇒ T ⟧ ρ  a  = ⟦ Γ , x:S ⊢ t : T ⟧ (ρ , a)
    ⟦ Γ ⊢ r s : T ⟧ ρ = (⟦ Γ ⊢ r : S ⇒ T ⟧ ρ) (⟦ Γ ⊢ s : S ⟧ ρ)

Before moving forward, we introduce the record we will use to
represent interpretations of types and contexts in System T.
For now, we are only including the interpretation of a context
as an environment, as our interpretation of types will change
subtly to better fit our algorithm for normalization by
evaluation ─ this is also why we have only discussed evaluation
at a high level.

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

The key idea behind normalization by evaluation is that we have
inherently performed some normalization of the term `t` in its
evaluation -- if `t` was an application `r s`, we are actually
performing that application and reducing the term. Normalization by
evaluation as an algorithm takes advantage of this fact.

An issue with this view is that evaluation is not actually giving us the normal
form of a term, but rather its meaning as a semantic object in our meta language.
An algorithm for normalization by evaluation would need a way to to convert a
semantic object in our meta language back into a term in the object language.

Instead, we want to evaluate (i.e. normalize) the parts of the expression
that actually _can_ be evaluated (such as function application), while leaving
the parts that cannot intact. Under this view, normalization by evaluation
becomes the evaluation of an expression with unknowns (i.e. variables) to
another, possibly simplified, expression with unknowns.

To get this behavior, we make a subtle change to the "meaning" of a term
in the meta language -- instead of terms of type `nat` mapping to the
Agda data type for natural numbers, we will evaluate them to their normal
form.

This is a subtle distinction with a significant impact on the algorithm
we will define. We can now easily convert back to the object language,
because in technicality we never left it to begin with.

More concretely, we will be mapping a term `Γ ⊢ t : T` to an Agda data
type used to represent a term in its normal form. Terms in their normal
form (normal terms) will be defined mutually with terms that are blocked
on evaluation because they are unknown (neutral terms).

```agda
data Nf : (T : Type) → (Γ : Ctx) → Γ ⊢ T → Set -- Normal terms
data Ne (T : Type) (Γ : Ctx) : Γ ⊢ T → Set     -- Neutral terms
```

Now, the interpretation of a term of type `nat` is what we will want it to be to
define a suitable algorithm for normalization by evaluation:

    ⟦ nat ⟧ = Nf nat

Note that our definition of normal terms is indexed both by a type and a
context, yet here the interpretation of a type is only indexed by the type
itself. We will get to this later, but it is for this reason that we have
not yet written this implementation out in Agda. For now, we can give
an initial sketch of the algorithm, using a _reflection_ function `↑ᵀ` that
maps neutral terms of type `T` to semantic objects in `⟦ T ⟧`, and a
_reification_ function `↓ᵀ` for mapping a semantic object in `⟦ T ⟧` to normal forms
 of type `T`:

Putting all of these pieces together, we can present (in pseudo-code)
what an algorithm for normalization by evaluation would do.

    ⟦ nat ⟧ = Nf nat

    ↑ᵀ ∈ Ne T → ⟦ T ⟧
    ↑ⁿᵃᵗ 𝓊 = 𝓊
    ↑ˢ⃗ᵗ 𝓊 (a ∈ ⟦ S ⟧) = ↑ᵀ (𝓊 𝓋) , 𝓋 = ↓ˢ a
    
    ↓ᵀ ∈ ⟦ T ⟧ → Nf T
    ↓ⁿᵃᵗ 𝓋 = 𝓋
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
can see how our new interpretation of the type `nat` has benefitted us: we are
able to evaluate a term, leaving its unknowns "untouched", and once we have
finished evaluating the term, we are able to convert it back into our object
language.

As an initial step in formally defining this algorithm, we can introduce
the rules for normal and neutral terms in Agda. Going forward, we will be
using 𝓊 (for "unknown") to refer to neutral terms and 𝓋 (for "value") to
refer to normal terms.

Neutral terms are normal terms in their blocked form. Variables are the "base
case" for blocked terms. Application on an unknown function to a normal term is
also blocked, as is recursion on an unknown natural. blocked terms.

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
only ever be a need to use a placeholder value at our base type `nat`. For
liftable normals, we can fallback to using `zero` (which is a valid normal term)
instead of using our placeholder value. We allow ourselves this convenience
because in proving the soundness of normalization by evaluation, we will
be proving that neither the placeholder value nor the fallback of `zero` will
actually be used.

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

The actual interpretation of the base type `nat` will in fact be an extension to
Agda's natural numbers that embeds liftable neutrals.

```agda
data ℕ̂ : Set where
  zero : ℕ̂
  suc : ℕ̂ → ℕ̂
  ne : Ne^ nat → ℕ̂

instance
  ⟦Type⟧ : Interpretation Type
  Interpretation.⟦ ⟦Type⟧ ⟧ nat = ℕ̂
  Interpretation.⟦ ⟦Type⟧ ⟧ (S ⇒ T) = ⟦ S ⟧ → ⟦ T ⟧
```

We want a way to reify Agda expressions of type `ℕ̂`, for which we will define a
function `↓ℕ̂`. It is here that given an incompatible context that results in the
embedded liftable neutral being undefined, it will be necessary fallback to
`zero`. Once again, this case will be irrelevant and we will prove that it will
never actually be used in the algorithm for normalization by evaluation.

```agda
↓ℕ̂ : ⟦ nat ⟧ → Nf^ nat
↓ℕ̂ zero = zero^ where
  zero^ = (λ _ → ⟨ zero , nf-zero ⟩)
↓ℕ̂ (suc n) = suc^ (↓ℕ̂ n) where
  suc^ : Nf^ nat → Nf^ nat
  suc^ 𝓋̂ Γ =
    let ⟨ 𝓋 , pf ⟩ = 𝓋̂ Γ in
    ⟨ suc · 𝓋 , nf-suc pf ⟩
↓ℕ̂ (ne 𝓊̂) Γ with 𝓊̂ Γ
...            | inj₁ ⟨ 𝓊 , pf ⟩ = ⟨ 𝓊 , nf-neutral pf ⟩
...            | inj₂ tt         = ⟨ zero , nf-zero ⟩
```


Next up is perhaps the most important part of normalization by evaluation,
reflection and reification. These are mutually recursive, and will each be
defined by induction on the type `T`.

```agda

mutual
  ↑ᵀ : {T : Type} → Ne^ T → ⟦ T ⟧
  ↑ᵀ {nat} 𝓊̂ = ne 𝓊̂
  ↑ᵀ {S ⇒ T} 𝓊̂ a = ↑ᵀ (𝓊̂ ·^ 𝓋̂) where 𝓋̂ = ↓ᵀ a

  ↓ᵀ : {T : Type} → ⟦ T ⟧ → Nf^ T
  ↓ᵀ {nat} = ↓ℕ̂
  ↓ᵀ {S ⇒ T} f Γ =
    let ⟨ 𝓋 , pf ⟩ = ↓ᵀ (f a) (Γ , S) in
    ⟨ ƛ 𝓋 , nf-abs pf ⟩
    where a = ↑ᵀ (𝓍̂ S Γ)
```

For reification at function type, we use the following function which creates a
"fresh" variable for a context `Γ`. Really, this is just the de Brujin index `𝑍`
for a context `Γ, x:S`. This will be a liftable variable that can be used in
a context that is an extension of `Γ, x:S` (and is undefined otherwise). When
applied to an extension `Γ′` of `Γ, x:S` we can apply the extension renaming to
the de Brujin index `𝑍` to obtain its corresponding index in the extended
context.

```
  𝓍̂ : (S : Type) → Ctx → Ne^ S
  𝓍̂ S Γ Γ′
    with Γ′ ≤? (Γ , S)
  ...  | no _          = inj₂ tt
  ...  | yes pf        = inj₁ ⟨ # x , ne-var x ⟩ where x = ren 𝑍 (ren-≤ pf)
```

With these two functions in place, we can also define the reflection of a context
`Γ` into an environment. This will be the reflected environment over which a
typed term in the context `Γ` will be evaluated.

```agda
↑ᶜᵗˣ : ∀ (Γ : Ctx) → ⟦ Γ ⟧
↑ᶜᵗˣ ∅       = tt
↑ᶜᵗˣ (Γ , T) = ⟨ ↑ᶜᵗˣ Γ  , ↑ᵀ (𝓍̂ T Γ) ⟩
```

The interpretation of recursion in System T must work with liftable neutrals (as
the interpretation of `nat` has them embedded), for this which we can use
reflection and reification.

```agda
rec^ : ∀ {T : Type} → Nf^ T → Nf^ (nat ⇒ T ⇒ T) → Ne^ nat → Ne^ T
rec^ 𝓋̂z 𝓋̂s 𝓊̂ Γ with 𝓊̂ Γ
... | inj₂ tt           = inj₂ tt
... | inj₁ ⟨ 𝓊 , pf-𝓊 ⟩ =
  let ⟨ 𝓋z , pf-𝓋z ⟩ = 𝓋̂z Γ in
  let ⟨ 𝓋s , pf-𝓋s ⟩ = 𝓋̂s Γ in
  inj₁ ⟨ rec · 𝓋z · 𝓋s · 𝓊 , ne-rec pf-𝓋z pf-𝓋s pf-𝓊 ⟩

⟦rec⟧ : ∀ {T : Type} → ⟦ T ⇒ (nat ⇒ T ⇒ T) ⇒ nat ⇒ T ⟧
⟦rec⟧ z s zero       = z
⟦rec⟧ z s (suc n)    = s n (⟦rec⟧ z s n)
⟦rec⟧ {T} z s (ne 𝓊̂) =
  ↑ᵀ (rec^ 𝓋̂z 𝓋̂s 𝓊̂) where 𝓋̂z = ↓ᵀ z ; 𝓋̂s = ↓ᵀ s
```

Evaluation can now actually be defined in Agda, having been blocked by a lack of
an interpretation for primitive recursion. It is exactly as was shown earlier
in pseudo-code.

```agda
⟦_∋Γ⟧ : ∀ {Γ : Ctx} {T : Type} → Γ ∋ T → ⟦ Γ ⟧ → ⟦ T ⟧
⟦_∋Γ⟧ {Γ , T} 𝑍 ⟨ _ , a ⟩     = a
⟦_∋Γ⟧ {Γ , T} (𝑆 x) ⟨ ρ , _ ⟩ = ⟦ x ∋Γ⟧ ρ

⟦⊢_⟧ : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → ⟦ Γ ⟧ → ⟦ T ⟧
⟦⊢ zero ⟧ _  = zero
⟦⊢ suc ⟧ _   = suc
⟦⊢ rec ⟧ _   = ⟦rec⟧
⟦⊢ # x ⟧     = ⟦ x ∋Γ⟧
⟦⊢ ƛ t ⟧ ρ a = ⟦⊢ t ⟧ ⟨ ρ , a ⟩
⟦⊢ r · s ⟧ ρ = ⟦⊢ r ⟧ ρ (⟦⊢ s ⟧  ρ)
```

Finally, the algorithm for normalization by evaluation is as follows:

```agda
nbe : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → ∃[ t ] Nf T Γ t
nbe {Γ} t = ↓ᵀ (⟦⊢ t ⟧ (↑ᶜᵗˣ Γ)) Γ

nf : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → Γ ⊢ T
nf t = let ⟨ t′ , _ ⟩ = nbe t in t′
```

And here we have some examples of the algorithm in action, reusing our
examples from earlier.

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
nf-ex3 : nf ex3 ≡ (suc · (suc · # (𝑍)))
nf-ex3 with ex3
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
  ==→⟦≡⟧ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {ρ : ⟦ Γ ⟧}
         → t == t′
         → ⟦⊢ t ⟧ ρ ≡ ⟦⊢ t′ ⟧ ρ
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
completeness {Γ} t==t′ rewrite ==→⟦≡⟧ {ρ = ↑ᶜᵗˣ Γ} t==t′ = refl
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
ren≡[x]ᵣ : ∀ {Γ Δ : Ctx} {T : Type} {x : Δ ∋ T} {σᵣ : Ren Γ Δ}
         → # (ren x σᵣ) ≡ # x [ σᵣ ]ᵣ
ren≡[x]ᵣ {x = 𝑍} {σᵣ , y} = refl
ren≡[x]ᵣ {x = 𝑆 x} {σᵣ , y} = ren≡[x]ᵣ {x = x} {σᵣ}

-- Applying a shifted renaming to a variable is equivalent
-- to incrementing the original renaming of the variable's
-- lookup judgemnet:
--   # x [ σ ↥ ] ≡ 𝑆 (rename x σ) (where σ is a renaming substitution)
shift-var : ∀ {Γ Δ : Ctx} {S T : Type} {x : Γ ∋ T} {σᵣ : Ren Δ Γ}
          → # x [ subst-ren (_↥ᵣ {T = S} σᵣ) ] ≡ # (𝑆 (ren x σᵣ))
shift-var {x = 𝑍} {_ , _} = refl
shift-var {x = 𝑆 x} {σᵣ , _} = shift-var {x = x} {σᵣ}

-- Specialized version of the previous lemma
shift-rename : ∀ {Γ Δ : Ctx} {S T : Type} {x : Γ ∋ T} {σᵣ : Ren Δ Γ}
             → ren x (_↥ᵣ {T = S} σᵣ) ≡ 𝑆 (ren x σᵣ)
shift-rename {x = 𝑍} {_ , _} = refl
shift-rename {x = 𝑆 x} {σᵣ , _} = shift-rename {x = x} {σᵣ}

-- Renaming with the identity renaming has no effect
rename-id : ∀ {Γ : Ctx} {T : Type} {x : Γ ∋ T}
          → ren x ren-id ≡ x
rename-id {x = 𝑍} = refl
rename-id {x = (𝑆_ {_} {S} x)}
  rewrite shift-rename {S = S} {x = x} {σᵣ = ren-id} | rename-id {x = x} = refl

-- Shifting is commutative between renaming/substitution: a shifted
-- renaming substitution is equivalent to a substitution created from
-- a shifted renaming
shift-rename-subst : ∀ {Γ Δ : Ctx} {T : Type} {σᵣ : Ren Γ Δ}
                   → subst-ren (_↥ᵣ {T = T} σᵣ) ≡ _↥ {T = T} (subst-ren σᵣ)
shift-rename-subst {σᵣ = ∅} = refl
shift-rename-subst {T = T} {σᵣ = _,_ {S = S} σᵣ x}
  rewrite shift-rename-subst {T = T} {σᵣ = σᵣ}
        | ≡-sym (ren≡[x]ᵣ {x = x} {σᵣ = _↥ᵣ {T = T} ren-id})
        | shift-rename {S = T} {x = x} {σᵣ = ren-id}
        | rename-id {x = x}                                 = refl

-- Lemma for expanding an identity substitution once
id≡id↑,x : ∀ {Γ : Ctx} {T : Type} → subst-id {Γ , T} ≡ (_↥ {T = T} subst-id , # 𝑍)
id≡id↑,x {∅} = refl
id≡id↑,x {Γ , T} {S}
  rewrite id≡id↑,x {Γ} {T}
        | shift-rename-subst {Γ , T} {Γ} {S} {σᵣ = ren-id ↥ᵣ} = refl

-- The identity substititon has no effect
[id]-identity : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
              → t [ subst-id ] ≡ t
[id]-identity {t = zero} = refl
[id]-identity {t = suc} = refl
[id]-identity {t = rec} = refl
[id]-identity {t = # 𝑍} = refl
[id]-identity {t = # (𝑆_ {_} {S} x)}
  rewrite shift-var {S = S} {x = x} {σᵣ = ren-id} | rename-id {x = x} = refl
[id]-identity {Γ} {T} {ƛ_ {S} t}
  rewrite ≡-sym (id≡id↑,x {Γ} {S}) | [id]-identity {t = t} = refl
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

  subst-compose-↥ : ∀ {Γ₁ Γ₂ Γ₃ : Ctx} {S : Type} {τ : Sub Γ₁ Γ₂}
                      {σ : Sub Γ₂ Γ₃} {s : Γ₁ ⊢ S}
                  → (σ ↥) ∘ (τ , s) ≡ σ ∘ τ

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
weaken-incr≡↥ : ∀ {Γ Γ′ : Ctx} {Γ′≤Γ : Γ′ ≤ Γ} {S T : Type} {t : Γ ⊢ T}
         → S ↑⊢ (t [ weaken Γ′≤Γ ]) ≡ t [ subst-ren (ren-≤ Γ′≤Γ ↥ᵣ) ]
weaken-incr≡↥ {Γ′≤Γ = ≤-id} {t = t} rewrite [id]-identity {t = t} = refl
weaken-incr≡↥ {Γ′≤Γ = ≤-ext {T = S₁} Γ′≤Γ} {S₂} {t = t}
  rewrite ≡-sym (weaken-incr≡↥ {Γ′≤Γ = Γ′≤Γ} {S₁} {t = t})
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

The logical relation `Γ ⊢ t : T Ⓡ a` will be defined inductively on types. For
Agda's termination checking, we will need to define the logical relation at type
`nat` separately. At type `nat`, the relation is defined as:

      Γ ⊢ t : nat Ⓡ 𝓋̂ ⇔ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = 𝓋̂(Γ′) : nat

In other words, `t` is logically related to a semantic object `𝓋̂ ∈ ℕ̂` if and only
if the term is definitionally equal to `𝓋̂` when lifted to any context `Γ′` that
is an extension of `Γ`.

In Agda, we define this relation as `_Ⓝ_` We define `Ⓝ` mutually with `==ℕ̂`, a
relation representing the condition `Γ′ ⊢ t = 𝓋̂(Γ′) : nat` we have just shown,
which lifts definitional equality to be over naturals with embedded liftable
neutrals, as was done with `_==^_`.

```agda
mutual
  _Ⓝ_ : ∀ {Γ : Ctx} → Γ ⊢ nat → ⟦ nat ⟧ → Set
  _Ⓝ_ {Γ} n 𝓋̂ =
    ∀ {Γ′ : Ctx}
    → (Γ′≤Γ : Γ′ ≤ Γ)
      ---------------
    → Γ′≤Γ ≤⊢ n ==ℕ̂ 𝓋̂

  _==ℕ̂_ : ∀ {Γ : Ctx} → Γ ⊢ nat → ⟦ nat ⟧ → Set
  _==ℕ̂_ {Γ} t zero = t == zero
  _==ℕ̂_ {Γ} t (suc 𝓋̂) = ∃[ n ] t == suc · n × n Ⓝ 𝓋̂
  _==ℕ̂_ {Γ} t (ne 𝓊̂) = t ==^ 𝓊̂
```

<!---
```
infix 4 _Ⓝ_
infix 3 _==ℕ̂_
```
--->

For the last part of our proof, we will be generalizing `Ⓡ` to relate more than
just terms and semantic objects, so we will be using a record type generalized
over any two Agda types to define the relation.

```agda
record Relation (A B : Set) : Set₁ where
  field
    rel : A → B → Set

open Relation ⦃...⦄ public

_Ⓡ_ : ∀ {A B : Set} ⦃ _ : Relation A B ⦄ → A → B → Set
_Ⓡ_ = rel
```

<!---
```
infix 4 _Ⓡ_
```
--->

#### Logical relation between terms and semantic objects

With these in place, we can start defining the logical relation `Ⓡ` between
terms and semantic objects by induction on types, using `Ⓝ` for the base type
`nat`. For function types, the relation is defined as:

    Γ ⊢ r : S → T Ⓡ f ⇔ ∀ Γ′ ≤ Γ. Γ′ ⊢ s : S Ⓡ a ⇒ Γ′ ⊢ r s : T Ⓡ f(a)

The relation is written so that it sort of expands functions, reducing our proof
that a functional term in System T is logically related to a function in Agda to
only having to prove that given related arguments, the functional term and the
function in Agda both produce related results. Again, this is generalized over
all extensions of the context `Γ` ─ while our final results will only be
concerned with the context `Γ`, to prove these results we will need the relation
to be strengthened in this way.

```agda
instance
  Ⓡ-Terms : ∀ {Γ : Ctx} {T : Type} → Relation (Γ ⊢ T) ⟦ T ⟧
  Relation.rel (Ⓡ-Terms {T = nat}) t 𝓋̂   = t Ⓝ 𝓋̂
  Relation.rel (Ⓡ-Terms {Γ} {S ⇒ T}) r f =
    ∀ {Γ′ : Ctx}
    → (Γ′≤Γ : Γ′ ≤ Γ)
    → ∀ {s : Γ′ ⊢ S} {a : ⟦ S ⟧}
    → s Ⓡ a
      -------------------------
    → (Γ′≤Γ ≤⊢ r) · s Ⓡ f a
```

As the logical relation between terms and semantic objects is defined using
definitional equality, it is transitive with respect to definitional equality.
We prove this using a postulated lemma that has been omitted, `==-subst`. With
`==-subst`, we postulate that if two terms are definitionally equal, the terms
with the same substitution applied are still definitionally equal. This is our
first proof using equational reasoning for definitional equality. As for most
proofs related to the logical relation `Ⓡ` between terms and semantic objects,
we prove it by induction on types, and do a case analysis at type `nat` on the
semantic object `a ∈ ℕ̂`.

```agda
==-Ⓡ-trans : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T} {a : ⟦ T ⟧}
           → t == t′
           → t Ⓡ a
             -------
           → t′ Ⓡ a
==-Ⓡ-trans {T = nat} {t} {t′} {zero} t==t′ pf Γ′≤Γ =
  begin
    Γ′≤Γ ≤⊢ t′
  ==⟨ sym (==-subst t==t′) ⟩
    Γ′≤Γ ≤⊢ t
  ==⟨ pf Γ′≤Γ ⟩
    zero
  ∎
==-Ⓡ-trans {T = nat} {t} {t′} {suc a} t==t′ pf Γ′≤Γ =
  let ⟨ n , ⟨ t==sn , n==a ⟩ ⟩ = pf Γ′≤Γ in
  let t′==sn = begin
                 Γ′≤Γ ≤⊢ t′
               ==⟨ sym (==-subst t==t′) ⟩
                 Γ′≤Γ ≤⊢ t
               ==⟨ t==sn ⟩
                 suc · n
               ∎
  in
  ⟨ n , ⟨ t′==sn , n==a ⟩ ⟩
==-Ⓡ-trans {T = nat} {t} {t′} {ne 𝓊̂} t==t′ pf {Γ′} Γ′≤Γ
  with 𝓊̂ Γ′          | pf Γ′≤Γ
... | inj₁ ⟨ 𝓊 , _ ⟩ | t==𝓊 =
  begin
    Γ′≤Γ ≤⊢ t′
  ==⟨ sym (==-subst t==t′) ⟩
    Γ′≤Γ ≤⊢ t
  ==⟨ t==𝓊 ⟩
    𝓊
  ∎
==-Ⓡ-trans {T = S ⇒ T} {r} {r′} r==r′ pf Γ′≤Γ sⓇa = ==-Ⓡ-trans r·s==r′·s r·sⓇfa
  where
    r·s==r′·s = app-compatible (==-subst r==r′) refl
    r·sⓇfa = pf Γ′≤Γ sⓇa
```

Additionally, because we have defined the relation so that its implication holds
for all extensions of a context, we can "weaken" the logical relation
`Γ ⊢ t : T Ⓡ a` for all `Γ′ ≤ Γ`, having that `Γ′ ⊢ t : T Ⓡ a` holds as well.
For this proof, we use another postulated lemma that weakening a term `t` twice
is equivalent to weakening it once with a composed weakening substitution.

```agda
Ⓡ-weaken : ∀ {Γ′ Γ : Ctx} {T : Type} {Γ′≤Γ : Γ′ ≤ Γ} {t : Γ ⊢ T} {a : ⟦ T ⟧}
      → t Ⓡ a
      → Γ′≤Γ ≤⊢ t Ⓡ a
Ⓡ-weaken {T = nat} {Γ′≤Γ} {t} pf Γ″≤Γ′
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

Our first lemma is:

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
define in Agda now as it will be a lemma we will need for proving the next
lemma we will introduce.

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

We will start by proving the first lemma focusing on each case of the proof
separately, before moving on to proving the second lemma. Again, the first
lemma is:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : T) ⇒ Γ ⊢ 𝓊 : T Ⓡ ↑ᵀ 𝓊̂

We prove this by induction on the type `T`. At type `nat`, our proof is
immediate, as `Γ ⊢ u : nat Ⓡ ↑ⁿᵃᵗ 𝓊̂` is defined as:

    ∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ) : nat

Which is exactly our given proof.

```agda
==^→Ⓡ↑ {T = nat} pf Γ′≤Γ = pf Γ′≤Γ
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
        begin
          Γ″≤Γ′ ≤⊢ (Γ′≤Γ ≤⊢ 𝓊) · s
        ==⟨ app-compatible (≡→== (weaken-compose Γ″≤Γ′ Γ′≤Γ 𝓊)) refl ⟩
          (Γ″≤Γ ≤⊢ 𝓊) · (Γ″≤Γ′ ≤⊢ s)
        ==⟨ app-compatible 𝓊==𝓊″ refl ⟩
          𝓊″ · (Γ″≤Γ′ ≤⊢ s)
        ==⟨ app-compatible refl s==↓ᵀaΓ″ ⟩
          𝓊″ · proj₁ (↓ᵀ a Γ″)
        ∎
        where
          s==↓ᵀaΓ″ = Ⓡ→==↓ sⓇa Γ″≤Γ′
          Γ″≤Γ = ≤-trans Γ″≤Γ′ Γ′≤Γ
```

This brings us to our second lemma:

    Γ ⊢ t : T Ⓡ a ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ᵀ a Γ′ : T

It will similarly be proven by induction on the type `T`. First, let us prove
the lemma for the type `nat`. At type `nat`, our lemma simplifies (by definition
of `Ⓡ`) to:

    (∀ Γ′ ≤ Γ. Γ′ ⊢ t : T = a (Γ′)) ⇒ ∀ Γ′ ≤ Γ. Γ′ ⊢ t = ↓ⁿᵃᵗ a Γ′ : T

We can prove this separately as a lemma, this time by induction on the semantic
object `a ∈ ℕ̂`, as `↓ⁿᵃᵗ` is defined by recursion on expressions of type `ℕ̂`.
The lemma makes up the first part of our proof, after which we can move on to
our inductive step.

```agda
==ℕ̂→==↓ᵀ : ∀ {Γ : Ctx} {n : Γ ⊢ nat} {a : ⟦ nat ⟧}
         → n ==ℕ̂ a
           -------------------
         → n == proj₁ (↓ᵀ a Γ)
==ℕ̂→==↓ᵀ {a = zero} pf with ↓ᵀ {nat} zero
... | _ = pf
==ℕ̂→==↓ᵀ {Γ} {a = suc a} ⟨ n , ⟨ m==sn , n==a ⟩ ⟩
  with ↓ᵀ {nat} (suc a) | ==ℕ̂→==↓ᵀ {a = a} (n==a ≤-id)
... | _                 | pf
  rewrite [id]-identity {t = n} = trans m==sn (app-compatible refl pf)
==ℕ̂→==↓ᵀ {Γ} {t} {ne 𝓊̂} pf
  with 𝓊̂ Γ           | pf
... | inj₁ ⟨ 𝓊 , _ ⟩ | t==𝓊 = t==𝓊

Ⓡ→==↓ {T = nat} {a = a} pf Γ′≤Γ = ==ℕ̂→==↓ᵀ {a = a} (pf Γ′≤Γ)
```

For our inductive step, we prove the lemma for terms of type `S → T`. Our lemma
now simplifies to:

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

The Agda proof for this case is as described, needing only a some substitution
lemmas to deal with the fact that in switching contexts, we are applying
weakening substitutions to our terms (we have left the proofs of these lemmas
out as well, as they are mostly a result of our formalization of
substitutions).

```agda
Ⓡ→==↓ {Γ′} {T = S ⇒ _} {t} {f} pf Γ′≤Γ =
  begin
    Γ′≤Γ ≤⊢ t
  ==⟨ η ⟩
    ƛ (S ↑⊢ Γ′≤Γ ≤⊢ t) · # 𝑍
  ==⟨
    abs-compatible (
      begin
        (S ↑⊢ Γ′≤Γ ≤⊢ t) · # 𝑍
      ==⟨ app-compatible subst-lemma refl ⟩
        (≤-ext Γ′≤Γ ≤⊢ t) [ subst-id ] · # 𝑍
      ==⟨ Ⓡ→==↓ (pf (≤-ext Γ′≤Γ) xⓇa) ≤-id ⟩
        proj₁ (↓ᵀ (f a) (Γ′ , S))
      ∎
  )⟩
    proj₁ (↓ᵀ f Γ′)
  ∎
  where
    a = ↑ᵀ {S} (𝓍̂ S Γ′)
    xⓇa = xⓇ↑ᵀ𝓍̂ {Γ′} {S}

    subst-lemma =
      ≡→== (≡-trans (weaken-incr≡↥ {Γ′≤Γ = Γ′≤Γ} {t = t}) (≡-sym [id]-identity))
```

Lastly, we can quickly derive the lemma `Γ , x:T ⊢ x : T Ⓡ ↑ᵀ 𝓍̂ Γ` used in the
previous lemma using `(∀ Γ′ ≤ Γ. Γ′ ⊢ 𝓊 = 𝓊̂(Γ′) : T) ⇒ Γ ⊢ 𝓊 Ⓡ ↑ᵀ 𝓊̂`. Again, we
use a lemma we have left out in the rendering that any proof of context
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
    with ren-≤ pf′
  ...| _ , _       = refl
```

Before moving forward to the last part of our overall proof that the normal form
of a term obtained by normaliztion by evaluation is definitionally equal, we
also need to show that  `Γ ⊢ rec : T → (nat → T → T) → nat → T Ⓡ ⟦rec⟧`, as one
of the terms that `t` can be in our desired property `Γ ⊢ t Ⓡ ⟦t⟧ ↑Γ` is `rec`.
Essentially, we need proof that our interpretation of `rec` is sound to prove
the overall soundness of normalization by evaluation. We omit this proof, as it
is rather involved, but it is again available in the source code.

```agda
recⓇ⟦rec⟧ : ∀ {Γ : Ctx} {T : Type} → rec {Γ} {T} Ⓡ ⟦rec⟧
```

<!---
```agda
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

recⓇ⟦rec⟧ Γ′≤Γ {z} {az} pf Γ″≤Γ′ {s} {as} pf′ Γ‴≤Γ″ {m} {suc an} pf″
  with pf″ ≤-id
... | ⟨ n , ⟨ m==san , nⓇan ⟩ ⟩
  rewrite [id]-identity {t = m} =
    ==-Ⓡ-trans (app-compatible refl (sym m==san))
      (==-Ⓡ-trans (sym β-rec-s) s·n·recⓇas·an·⟦rec⟧)
  where
    subst-lemma₁ = [id]-identity {t = Γ‴≤Γ″ ≤⊢ s}
    subst-lemma₂ = [id]-identity {t = n}

    rec·z·s·n = (Γ‴≤Γ″ ≤⊢ (Γ″≤Γ′ ≤⊢ rec · z) · s) · n

    ih : rec·z·s·n Ⓡ ⟦rec⟧ az as an
    ih = recⓇ⟦rec⟧ Γ′≤Γ pf Γ″≤Γ′ {s = s} pf′ Γ‴≤Γ″ {s = n} {an} nⓇan

    s·n·recⓇas·an·⟦rec⟧ : (Γ‴≤Γ″ ≤⊢ s) · n · rec·z·s·n Ⓡ as an (⟦rec⟧ az as an)
    s·n·recⓇas·an·⟦rec⟧ with pf′ Γ‴≤Γ″ {n} nⓇan ≤-id ih
    ... | pf
      rewrite subst-lemma₁ | subst-lemma₂ = pf

recⓇ⟦rec⟧ {_} {T} Γ′≤Γ {z} {az} pf Γ″≤Γ′ {s} {as} pf′ {Γ‴} Γ‴≤Γ″ {n} {ne 𝓊̂} pf″ =
  ==^→Ⓡ↑ rec==^rec^ where
    rec==^rec^ : ∀ {Γ⁗ : Ctx}
      → (Γ⁗≤Γ‴ : Γ⁗ ≤ Γ‴)
      → Γ⁗≤Γ‴ ≤⊢ (Γ‴≤Γ″ ≤⊢ (Γ″≤Γ′ ≤⊢ rec · z) · s) · n ==^ rec^ (↓ᵀ az) (↓ᵀ as) 𝓊̂
    rec==^rec^ {Γ⁗} Γ⁗≤Γ‴
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

        subst-lemma₁ = ≡-sym (weaken-incr≡↥ {Γ′≤Γ = Γ⁗≤Γ″} {S = nat} {t = s})
        subst-lemma₂ =
          ≡-sym (weaken-compose Γ⁗≤Γ‴ Γ‴≤Γ″ s)
        subst-lemma₃ = [id]-identity {t = T ↑⊢ nat ↑⊢ Γ⁗≤Γ‴ ≤⊢ Γ‴≤Γ″ ≤⊢ s}

        𝓍̂₁ = 𝓍̂ nat Γ⁗
        𝓍̂₂ = 𝓍̂ T (Γ⁗ , nat)

        s·x₁·x₂Ⓡas·↑ᵀ𝓍̂₁↑ᵀ𝓍̂₂ =
          pf′ Γ⁗,nat≤Γ⁗ {s = # 𝑍} {a = ↑ᵀ {nat} (𝓍̂ nat Γ⁗)} (xⓇ↑ᵀ𝓍̂ {Γ⁗} {nat})
            Γ⁗,nat,T≤Γ⁗,nat xⓇ↑ᵀ𝓍̂

        s·x₁·x₂==↓ᵀas·↑ᵀ𝓍̂₁·↑ᵀ𝓍̂₂ :
          (T ↑⊢ nat ↑⊢ Γ⁗≤Γ‴ ≤⊢ Γ‴≤Γ″ ≤⊢ s) · # (𝑆 𝑍) · # 𝑍 ==
            proj₁ (↓ᵀ (as (↑ᵀ 𝓍̂₁) (↑ᵀ 𝓍̂₂)) (Γ⁗ , nat , T))
        s·x₁·x₂==↓ᵀas·↑ᵀ𝓍̂₁·↑ᵀ𝓍̂₂
          with s·x₁·x₂Ⓡas·↑ᵀ𝓍̂₁↑ᵀ𝓍̂₂
        ... | pf-Ⓡ
          with Ⓡ→==↓ pf-Ⓡ ≤-id
        ... | pf-==↓ᵀ
          rewrite subst-lemma₁ | subst-lemma₂ | subst-lemma₃ = pf-==↓ᵀ

        subst-lemma₄ = ≡-sym (weaken-compose Γ⁗≤Γ‴ Γ‴≤Γ′ z)
        subst-lemma₅  = ≡-sym (weaken-compose Γ‴≤Γ″ Γ″≤Γ′ z)

        z==↓ᵀaz : Γ⁗≤Γ‴ ≤⊢ Γ‴≤Γ″ ≤⊢ Γ″≤Γ′ ≤⊢ z == proj₁ (↓ᵀ az Γ⁗)
        z==↓ᵀaz
          with Ⓡ→==↓ {Γ⁗} pf (≤-trans Γ⁗≤Γ‴ Γ‴≤Γ′)
        ... | pf
          rewrite subst-lemma₄ | subst-lemma₅ = pf
```
--->

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

The relation `Γ ⊢ σ : Δ Ⓡ ρ` between a parallel substitution `Γ ⊢ σ : Δ` and an
environment `ρ ∈ ⟦ Δ ⟧` will be defined inductively, though this time by
induction on `σ`.

A substitution from the empty context is always logically related to an empty
environment, while an extension to a substition `(σ , s / x)` is logically
related to an environment `(ρ , a)` if `σ` is logically related to `ρ` and `s`
is logically related to `a`.

```agda
instance
  Ⓡ-Sub : ∀ {Γ Δ : Ctx} → Relation (Sub Γ Δ) (⟦ Δ ⟧)
  Relation.rel Ⓡ-Sub ∅ tt              = ⊤
  Relation.rel Ⓡ-Sub (σ , s) ⟨ ρ , a ⟩ = σ Ⓡ ρ × s Ⓡ a
```

A consequence of defining the logical relation between substitutions and
environments by induction on `σ` is that we have that a logical relation for a
shifted substitution holds if the logical relation holds for the original
substitution. Intuitively, this makes sense because our relation is really only
concerned with the context `Δ`, which remains unchanged between a shifted
substitution `Γ , x:T ⊢ σ ↑ : Δ` and the original substitution `Γ ⊢ σ : Δ`.
This lemma (specifically its special case for a renaming substitution, which
is easier to prove) will come in handy later on. We can prove it by induction
on the renaming substitution itself. Here again we use some substitution lemmas
whose definitions are omitted.

```agda
Ⓡ-↥ : ∀ {Γ Δ : Ctx} {T : Type} {σᵣ : Ren Γ Δ} {ρ : ⟦ Δ ⟧}
      → subst-ren σᵣ Ⓡ ρ
      → subst-ren (_↥ᵣ {T = T} σᵣ) Ⓡ ρ
Ⓡ-↥ {σᵣ = ∅} pf                                   = tt
Ⓡ-↥ {T = T} {σᵣ = _ , x} {⟨ _ , a ⟩} ⟨ pf , xⓇa ⟩ = ⟨ Ⓡ-↥ pf , ↑⊢xⓇa ⟩
  where
    subst-lemma₁ = shift-var {S = T} {x = x} {σᵣ = ren-id}
    subst-lemma₂ = rename-id {x = x}

    Γ,T≤Γ = ≤-ext {T = T} ≤-id

    ↑⊢xⓇa : # (𝑆 x) Ⓡ a
    ↑⊢xⓇa
      with Ⓡ-weaken {Γ′≤Γ = Γ,T≤Γ} {t = # x} xⓇa
    ... | pf
      rewrite subst-lemma₁ | subst-lemma₂ = pf
```

A generalization of this is, similarly as for logical relations between terms
and semantic objects, that if a logical relation holds between a substitution
and an environment, it holds for any weakening of the substitution (as weakening
is really a series of shifts). We prove this by induction on the substitution,
applying the `Ⓡ-weaken` lemma for the logical relation between terms and
semantic objects for each term in the substitution.

```agda
Ⓡ-weaken′ : ∀ {Γ′ Γ Δ : Ctx} {Γ′≤Γ : Γ′ ≤ Γ} {σ : Sub Γ Δ} {ρ : ⟦ Δ ⟧}
        → σ Ⓡ ρ
        → σ ∘ (weaken Γ′≤Γ) Ⓡ ρ
Ⓡ-weaken′ {σ = ∅} x                            = tt
Ⓡ-weaken′ {Γ′≤Γ = Γ′≤Γ} {σ , s} ⟨ σⓇρ , sⓇa ⟩ =
  ⟨ Ⓡ-weaken′ {Γ′≤Γ = Γ′≤Γ} σⓇρ , Ⓡ-weaken {Γ′≤Γ = Γ′≤Γ} sⓇa ⟩
```

These two lemmas will be necessary for our proofs, which we are now ready to
begin laying out. We introduce the semantic typing judgement `Γ ⊨ t : T`:

```agda
_⊨_ : ∀ {T : Type} → (Γ : Ctx) → Γ ⊢ T → Set
_⊨_ {T} Γ t =
  ∀ {Δ : Ctx} {σ : Sub Δ Γ} {ρ : ⟦ Γ ⟧}
  → σ Ⓡ ρ
    -------
  → t [ σ ] Ⓡ ⟦⊢ t ⟧ ρ
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
logically related to, using our proof that `Γ ⊢ σ : Δ Ⓡ ρ`). Application follows
from our inductive hypotheses, leaving us at the abstraction case, which is the
most complicated to prove.

In the case of an abstraction `Γ ⊢ λx. t : S → T`, we want to prove:
    Γ ⊢ σ : Δ Ⓡ ρ ⇒
      Γ ⊢ (λx. t) [ σ ] : S → T Ⓡ ⟦ Γ ⊢ λx. t : S → T ⟧ ρ

By the definition of the application of a substitution to an abstraction, as
well as the definition of evaluation of an abstraction, this simplifies to:

    Γ ⊢ σ : Δ Ⓡ ρ ⇒
      Γ ⊢ λx. t [ σ ↥ , x / x ] : S → T Ⓡ f
        (where f = λ a → ⟦ Γ , x: S ⊢ t : T ⟧ (ρ , a))

We can also expand this using the definition of `Ⓡ` for functions (and
immediately reducing the application of `f` to `a`):

    Γ ⊢ σ : Δ Ⓡ ρ ⇒
      ∀ Γ′ ≤ Γ. Γ′ ⊢ s : S Ⓡ a ⇒
        Γ′ ⊢ (λx. t [ σ ↥ , x / x ]) · s : T Ⓡ ⟦ Γ , x:S ⊢ t : T ⟧ (ρ , a)

Already, this is a tricky property to parse. To start, we can use our lemma
that `Ⓡ` is transitive with respect to definitional equality, and use the `β-ƛ`
rule to reduce `(λx. t [ σ ↑ , x/x ]) · s` to `t [ σ ↑ , x / x ] [s / x]`. Now,
we need only prove:

    Γ′ , x:S ⊢ t [ σ ↥ , x / x ] [ s / x ] : T Ⓡ ⟦ Γ , x:S ⊢ t : T ⟧ (ρ , a)

Here, we can use a substitution lemma to reduce these two substitutions, giving
us:

    Γ′ , x:S ⊢ t [ σ ↥ , s / x ] : T Ⓡ ⟦ Γ , x:S ⊢ t : T ⟧ (ρ , a)

Now, the property we want to show actually looks like our induction hypothesis.
With it, we have that we only need to show that:

     Γ′ , x:S ⊢ (σ ↥ , s / x) : Δ Ⓡ (ρ , a)

This expands to proving both:

     Γ′ , x:S ⊢ σ ↥ : Δ Ⓡ ρ
     Γ′ ⊢ s : S Ⓡ a

The first follows from our earlier lemma that if a substitution is logically
related to an environment, then so is a shifting of the substitution. The
second property follows from our given proof. With that, our abstraction case is
proven. In reality, there are a few other substitution lemmas that our
formalization forces us to use, but they are mostly irrelevant to the proofs
themselves at a high-level. [^1]

```agda
fundamental-lemma : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
                  → Γ ⊨ t
fundamental-lemma {t = zero} σⓇρ _ = refl
fundamental-lemma {t = suc} σⓇρ Δ′≤Δ {s} {a} pf {Δ″} Δ″≤Δ′ =
  ⟨ Δ″≤Δ′ ≤⊢ s , ⟨ refl , s==a ⟩ ⟩
  where
    s==a : ∀ {Δ‴ : Ctx} → (Δ‴≤Δ″ : Δ‴ ≤ Δ″) → Δ‴≤Δ″ ≤⊢ Δ″≤Δ′ ≤⊢ s ==ℕ̂ a
    s==a Δ‴≤Δ″
      with pf (≤-trans Δ‴≤Δ″ Δ″≤Δ′)
    ... | pf
      rewrite weaken-compose Δ‴≤Δ″ Δ″≤Δ′ s = pf
fundamental-lemma {t = rec {T}} _ = recⓇ⟦rec⟧
fundamental-lemma {t = # 𝑍} {σ = _ , _ } {⟨ _ , _ ⟩} ⟨ _ , xⓇa ⟩ = xⓇa
fundamental-lemma {t = # (𝑆 x)} {σ = _ , _} {⟨ _ , _ ⟩} ⟨ σⓇρ , _ ⟩ =
  fundamental-lemma {t = # x} σⓇρ
fundamental-lemma {t = ƛ t} {σ = σ} {ρ} σⓇρ Γ′≤Γ {s} {a} sⓇa =
  ==-Ⓡ-trans (sym β-ƛ) t[σ↥,x/x][s/x]Ⓡ⟦t⟧⟨ρ,a⟩
  where
    subst-lemma₁ =
      subst-compose {τ = subst-id , s} {weaken Γ′≤Γ ↥ , # 𝑍} {t [ σ ↥ , # 𝑍 ]}
    subst-lemma₂ =
     subst-compose {τ = ((weaken Γ′≤Γ ↥) ∘ (subst-id , s)) , s} {σ ↥ , # 𝑍} {t}

    t[σ↥,x/x] = t [ σ ↥ , # 𝑍 ] [ weaken Γ′≤Γ ↥ , # 𝑍 ]

    subst-lemma₃ = subst-compose-↥ {τ = subst-id} {weaken Γ′≤Γ} {s}
    subst-lemma₄ = subst-compose-↥ {τ = weaken Γ′≤Γ ∘ subst-id} {σ} {s}
    subst-lemma₅ = id-compose-identity {σ = weaken Γ′≤Γ}

    σ′ = ((σ ↥) ∘ (((weaken Γ′≤Γ ↥) ∘ (subst-id , s)) , s))

    σ′Ⓡρ : σ′  Ⓡ ρ
    σ′Ⓡρ rewrite subst-lemma₃ | subst-lemma₄ | subst-lemma₅ =
      Ⓡ-weaken′ {Γ′≤Γ = Γ′≤Γ} σⓇρ

    t[σ↥,x/x][s/x]Ⓡ⟦t⟧⟨ρ,a⟩ : t[σ↥,x/x] [ s /x] Ⓡ ⟦⊢ t ⟧ ⟨ ρ , a ⟩
    t[σ↥,x/x][s/x]Ⓡ⟦t⟧⟨ρ,a⟩ rewrite subst-lemma₁ | subst-lemma₂ =
        fundamental-lemma {t = t} ⟨ σ′Ⓡρ , sⓇa ⟩
fundamental-lemma {t = r · s} {σ = σ} σⓇρ
  with fundamental-lemma {t = r} σⓇρ | fundamental-lemma {t = s} σⓇρ
... | Γ⊨r                             | Γ⊨s
  with Γ⊨r ≤-id Γ⊨s
... | pf
  rewrite [id]-identity {t = r [ σ ]} = pf
```

Separately, we have that the identity substitution is logically related to
our environment of reflected variables, `Γ ⊢ id : Γ Ⓡ ↑Γ`. We prove this by
induction, again using the lemma that `Γ, x:T ⊢ x : T Ⓡ ↑ᵀ 𝓍̂ Γ` for every
variable being substituted for itself. For our inductive step:

    Γ , x : T ⊢ id ↥ , x / x : Γ , x : T`

The inductive hypothesis actually gives us proof that `Γ ⊢ id : Γ Ⓡ ↑Γ`. What
we really want is proof that `Γ , x : T ⊢ id ↥ : Γ Ⓡ Γ`. Here, we use our lemma
that if a logical relation holds for a substitution and an environment, it also
holds for a shifting of the substitution. This transforms our inductive
hypothesis into our goal.

```agda
idⓇ↑Γ : ∀ {Γ : Ctx}
       → subst-id Ⓡ (↑ᶜᵗˣ Γ)
idⓇ↑Γ {∅}     = tt
idⓇ↑Γ {Γ , T} = ⟨ Ⓡ-↥ {T = T} idⓇ↑Γ , xⓇ↑ᵀ𝓍̂ ⟩
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
  rewrite [id]-identity {t = t [ subst-id ]}
        | [id]-identity {t = t}              = t==↓ᵀ⟦t⟧↑Γ
```

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
