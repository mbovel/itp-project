# Interactive Theorem Proving Project, EPFL, Spring 2024

*Matt Bovel, Samuel Chassot*

## Abstract

We implement, verify, and compare increasingly complete decision procedures for the theory of equality in the Coq proof assistant. We start with a decision procedure for equality only (reflexive-symmetric-transitive closure), then extend it to uninterpreted functions (congruent closure), initially for single argument functions and later for multiple arguments. Subsequently, we introduce support for normalization to address commutativity. If time permits, we plan to extend our framework to handle lists and to provide a mechanized worst-case analysis of the decision procedures.

## Background

**Definition:** the *reflexive-symmetric-transitive (RST)* closure $rst(R)$ of a relation $R$ can be inductively defined by the following properties:

- Axioms: $R \subseteq rst(R)$
- Reflexivity: $\forall a. \; (a, a) \in rst(R)$
- Symmetry: $\forall a, b. \; (a, b) \in rst(R) \Rightarrow (b, a) \in rst(R)$
- Transitivity: $\forall a, b, c. \;\left((a, b) \in rst(R) \land (b, c) \in rst(R) \right) \Rightarrow (a, c) \in rst(R)$

The [*Union-Find*](https://en.wikipedia.org/wiki/Disjoint-set_data_structure) data structure can be used to efficiently compute this closure. It manages a partition of elements into disjoint sets, supporting efficient union and find operations allowing to query the equivalence classes.

**Definition**: the *congruent closure* `C'` of a relation `C` is the RST closure, with an additional axiom for uninterpreted functions:

- RST: $rst(C) \subseteq C'$
- Congruence: $\forall f, a, b. \; (f(a), f(b)) \in C' \Rightarrow (a, b) \in C'$

[The *congruent closure algorithm* is a decision procedure for the congruent closure relation. This procuedure, described notably in [Nelson, 1981] relies on the Union-Find mechanism, but adds an indirection: it maintains equivalences between class identifiers. This, and using hash-consing allows to manage equivalences not just between elements but also between function applications.]

## Implementation

We propose to start with an implementation equivalence as an inductive definition parametrized by a relation `R` represented as a `list (A * A)` of pairs of elements of type `A`:

```coq
Inductive eq {A : Type} (axms : list (A * A)) : A -> A -> Prop :=
  | eq_axms: forall x y: A, In (x, y) axms -> eq axms x y
  | eq_refl: forall x: A, eq axms x x
  | eq_sym: forall x y: A, eq axms y x -> eq axms x y
  | eq_trans: forall x y z: A, eq axms x y -> eq axms y z -> eq axms x z.
```

## Timeline

- Project week 4: definitions, and decision procedure for equality only.
- Project week 5: decision procedure for congruent closure with single argument.
- Project week 6: decision procedure for congruent closure with multiple arguments.
- Project week 7: decision procedure with a normalization step.
- Bonus if time permits: decision procedure for lists, and worst-case analysis.

Deliverables: Coq code for each week.

## References

- [Techniques for Program Verification, Nelson, 1981](https://people.eecs.berkeley.edu/~necula/Papers/nelson-thesis.pdf): original paper on congruent closure algorithm.
- [Intro to EGraphs, Colab](https://colab.research.google.com/drive/1tNOQijJqe5tw-Pk9iqd6HHb2abC5aRid): nice introduction to EGraphs.
- [EGG (EGraphs Good)](https://egraphs-good.github.io): combining EGraphs and equality saturation to implement optimizers.
- [Proof-producing Congruence Closure](https://www.cs.upc.edu/~oliveras/rta05.pdf)
- [Project: congruence closure algorithm in Coq using dependent types](https://github.com/knuthingmuch/congruence-closure): similar course project from 2019.
