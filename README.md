# Normalization by Evaluation

This repository contains a formalization of normalization by evaluation for the simply typed lambda calculus.

It is based largely on Chapter 2 of Andreas Abel's habilitation thesis,
[Normalization by Evaluation: Dependent Types and Impredicativity](https://www.cse.chalmers.se/~abela/habil.pdf).

Some of the lemmas used (substitutions can be composed, the identity substitution is an identity,
substitutions preserve meaning) are adapted from the [Substitution](https://plfa.github.io/Substitution/)
and [Soundness](https://plfa.github.io/Soundness/) chapters of PLFA.

It is intended to be read as a "tutorial" in normalization by evaluation (available [here](https://emmanueljs1.github.io/nbe/NbE.html),
going over a representation of STLC first and then introducing the algorithm itself along with proofs of the algorithm's completeness and soundness.
