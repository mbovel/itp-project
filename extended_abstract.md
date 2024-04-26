# Interactive Theorem Proving Project, EPFL, Spring 2024

*Matt Bovel, Samuel Chassot*

## Abstract

We implement, verify, and compare increasingly complete decision procedures for the theory of equality in the Coq proof assistant. We start with a decision procedure for equality only (reflexive-symmetric-transitive closure), then extend it to uninterpreted functions (congruent closure), initially for single argument functions and later for multiple arguments. Subsequently, we introduce support for commutativity by adding a normalization step. If time permits, we plan to also extend our framework to handle lists and to provide a mechanized worst-case analysis of the decision procedures performance.

## Motivation

Congruence closure is essential for many verification tasks, including in SMT solvers, symbolic execution engines, or the `congruence` tactic in Coq. Our main goal is to better understand the mechanisms behind automatic reasoning about equality by implementing and verifying decision procedures. Our novelty lies in simplifying existing methods to prioritize comprehensibility over performance. We hope to derive insights that can be shared in an instructional blog post or slide deck.

## Background

The *reflexive-symmetric-transitive (RST)* closure $rst(R)$ of a relation $R$ can be inductively defined by the following properties:

- Axioms: $R \subseteq rst(R)$
- Reflexivity: $\forall a. \; (a, a) \in rst(R)$
- Symmetry: $\forall a, b. \; (a, b) \in rst(R) \Rightarrow (b, a) \in rst(R)$
- Transitivity: $\forall a, b, c. \;\left((a, b) \in rst(R) \land (b, c) \in rst(R) \right) \Rightarrow (a, c) \in rst(R)$

The [*Union-Find*](https://en.wikipedia.org/wiki/Disjoint-set_data_structure) data structure can be used to efficiently compute this closure. It manages a partition of elements into disjoint sets, supporting efficient union and find operations allowing to query the equivalence classes.

The *congruent closure* `C'` of a relation `C` is the RST closure, with an additional axiom for uninterpreted functions:

- RST: $rst(C) \subseteq C'$
- Congruence: $\forall f, a, b. \; (f(a), f(b)) \in C' \Rightarrow (a, b) \in C'$

The *congruent closure algorithm* is a decision procedure for handling congruent closure relations, following ideas from [Nelson, 1981]. It works similarly to the union-find algorithm by managing equivalence classes for terms, but has additional machinery to handle the congruence axiom. When adding the equivalence of two elements, it *repairs* the classes by canonicalizing all terms that depend on the two elements.

## Implementation sketch

We propose to start with an implementation of equivalence as an inductive definition parametrized by a relation `R` represented as a `list (A * A)` of pairs of elements of type `A`:

```coq
Inductive eq {A : Type} (axms : list (A * A)) : A -> A -> Prop :=
  | eq_axms: forall x y: A, In (x, y) axms -> eq axms x y
  | eq_refl: forall x: A, eq axms x x
  | eq_sym: forall x y: A, eq axms y x -> eq axms x y
  | eq_trans: forall x y z: A, eq axms x y -> eq axms y z -> eq axms x z.
```

To start, we will implement a basic structure for managing equality using functions that will expose the `empty` function for initialization, `union` to add equivalences, and `equiv` to check equivalence of two terms.

With this structure, the main theorem to prove will be the following:

```coq
Axiom make_correct: forall axms x y,
    let ds := fold_left (fun ds axm => union ds (fst axm) (snd axm)) axms empty in
    eq axms x y <-> equiv ds x y = true.

```

which, in a nutshell, states that the relation expressed by the datastructure `ds` created using the axioms (i.e., a list of equivalences) is equivalent to the relation `eq` expressed by the inductive definition, which represents the reflexive-symmetric-transitive closure of the axioms.

## Organization

Approximate timeline for the project:

- Project week 4: definitions, and decision procedure for equality only (c.f. implementation of a disjoint-set data structure).
- Project week 5: decision procedure for congruent closure with single argument.
- Project week 6: decision procedure for congruent closure with multiple arguments.
- Project week 7: decision procedure with a normalization step.
- Bonus if time permits: decision procedure for lists, and worst-case analysis.

Deliverables: Coq code for each week.

Collaboration: we mainly plan to work in pair programming.

## References

- [Formalization of a persistent union-find data structure in Coq](https://www.lri.fr/~filliatr/puf/)
- [A Simple, Probably-Not-Exp-Time Disjoint Set in Coq](https://www.philipzucker.com/simple-coq-union-find/)
- [Techniques for Program Verification, Nelson, 1981](https://people.eecs.berkeley.edu/~necula/Papers/nelson-thesis.pdf): original paper on congruent closure algorithm.
- [Intro to EGraphs, Colab](https://colab.research.google.com/drive/1tNOQijJqe5tw-Pk9iqd6HHb2abC5aRid): nice introduction to EGraphs.
- [EGG (EGraphs Good)](https://egraphs-good.github.io): combining EGraphs and equality saturation to implement optimizers.
- [Proof-producing Congruence Closure](https://www.cs.upc.edu/~oliveras/rta05.pdf)
- [Project: congruence closure algorithm in Coq using dependent types](https://github.com/knuthingmuch/congruence-closure): similar course project from 2019.
