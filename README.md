# Lagrange's Theorem in Lean 4

A formalisation of **Lagrange's Theorem** for finite groups in Lean 4, written as a self-contained learning exercise.

## Dependencies

This project relies on [Lean 4 and `elan`](https://lean-lang.org/install/). 

## Overview

Rather than relying on Mathlib's high-level group theory library (such as `Subgroup.index` or `Subgroup.card_mul_index`), this project builds the proof largely from scratch. 

### Built from scratch:
* Left cosets and some of their basic properties (pairwise disjointness and partitioning the group) are defined and proved manually.
* Explicit bijections showing that every coset has the same cardinality as the original subgroup.
* Combining the partition and bijection results to prove that the order of a subgroup divides the order of the finite group (one version of Lagrange's Theorem).
* Obtaining, as a corollary of the above, that the order of any element of the finite group divides the order of the whole group (another version of Lagrange's Theorem).

### Mathlib dependencies:
To avoid getting too bogged down in foundational set/number theory, a small number of standard Mathlib definitions and lemmas are used:
* Basic `Group`, `Subgroup`, and `Fintype` structures
* The order of an element (`orderOf g`) and cyclic subgroups (`Subgroup.zpowers g`)
* The standard lemma proving the above two are of equal cardinality (`Nat.card_zpowers`, $\abs{g} = \abs{\langle g \rangle}$).

