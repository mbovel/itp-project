# Interactive Theorem Proving Project, EPFL, Spring 2024

*Matt Bovel, Samuel Chassot*

## Abstract

We implement, verify and compare increasingly complete decision procedures for the theory of equality in the Coq proof assistant. We start with a decision procedure for equality only (supporting reflexivity, symmetry, transitivity), then extend it to uninterpreted functions (congruent closure), and then maybe to lists, linear arithmetic or by supporting associativity, commutativity, or fragment of first-order logic. We might also evaluate the performance of the decision procedures both through theoretical worst-case analysis, and experimentally by extracting them and benchmarking them against existing SMT solvers.

## References

- [Techniques for Program Verification, Nelson, 1981](https://people.eecs.berkeley.edu/~necula/Papers/nelson-thesis.pdf)

## 2024-04-11: Discussion with Alexandre 

- Overview: project sounds nice, it's good that it is incremental and that we have a clear idea how to start. It's okay to not define all extensions now, and to see how the project evolves.
- Note: Coq uses a congruence closure algorithm for its `congruence` tactic.
- Note: to implement support for associativity and commutativity, we can normalize the terms by ordering the arguments of the functions. Coq does this for the `ring` tactic. Matt implemented something similar for Scala compile-time operations 2 years ago ;)
- Question: shallow or deep? See chapter 15 of the course book.
    - Deep: create an inductive type to represent the expressions.
    - Shallow: translate our input language directly to Coq terms, without defining an inductive type to represent the terms of the input language.
- Possible extension: make the procedure available as a Coq tactic. 3 ways to do this:
    - Write the tactic as an OCaml "plugin". Probably not verified, cannot re-use code written in Coq.
    - Write the tactic LTac. Slower, produce proofs for specific instances.
    - *proof by reflection*: http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html.
- Next step:
    - Start coding
    - April 23: Full project proposal (two-page extended abstract).
