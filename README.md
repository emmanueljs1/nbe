# System T

This repository contains a formalization of Chapter 2 of Andreas Abel's habilitation thesis,
[Normalization by Evaluation: Dependent Types and Impredicativity](https://www.cse.chalmers.se/~abela/habil.pdf).

It can be read in the following order:

1) [SystemT.agda](./SystemT.lagda.md)
    * Basic language constructs
    * Parallel substitutions
    * Definitional equality
    * Context extensions

2) [NbE.agda](./NbE.agda)
    * Normal terms / neutral terms
    * Liftable terms
    * Interpretation of types, terms, and contexts
    * NbE algorithm

3) [Soundness.agda](./Soundness.agda)
    * Kripke logical relation between terms and semantic objects
    * Kripe logical relation between substitutions and environments
    * Fundamental lemma
    * Proof of soundness of NbE
    
* The file [Lemmas.agda](./Lemmas.agda) contains a number of lemmas useful for proving soundness
