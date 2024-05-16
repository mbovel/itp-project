# Interactive Theorem Proving Project, EPFL, Spring 2024

*Matt Bovel, Samuel Chassot*


## Representation

```scala
// 1. Map from each element to its parent
class DisjointSet[A](val parents: Map[A, A] = Map.empty[A, A])

// 2. Map from each element to its equivalence class
class DisjointSet[A](val equivalences: Map[A, List[A]])

// 3. List of list where each list is an equivalence class
class DisjointSet[A](val classes: List[List[A]])

// 4. Map from each element to its representative directly
// c.f. flat representation
class DisjointSet[A](val parents: Map[A, A] = Map.empty[A, A])
```

We implemented 1., 2. and 4. in Scala.

In Coq, we tried 3 first, but it was too cumbersome to work with:

https://github.com/mbovel/itp-project/blob/2ae3a5bbb5bbe0a32ce586120b9711f65079082a/src/DisjointSet.v#L39-L41

We then switched to 4. Still cumbersome, but we managed to make progress :)

https://github.com/mbovel/itp-project/blob/2ae3a5bbb5bbe0a32ce586120b9711f65079082a/src/DisjointSet.v#L81-L83

## Coq structure

Let's take a step back and look at the structure of our Coq project.

Equality axiomatisation:

https://github.com/mbovel/itp-project/blob/7bc0a61bfe645bbe60b34dbe0152f6850ac5f708/src/Equivalence.v#L5-L9

Tried with types classes first:

https://github.com/mbovel/itp-project/blob/d738ba3a33debc28b965aa1278d682d609a33de3/src/DisjointSet.v#L8-L58

Then came back to modules:

https://github.com/mbovel/itp-project/blob/0345f50283ee9a9fe85e6d399b44540ea1361887/src/DisjointSet.v#L10-L35


## Implementation

https://github.com/mbovel/itp-project/blob/e59ff114b69002f4d00e14c2cc81f53cf734748a/src/DisjointSet.v#L82-L89

https://github.com/mbovel/itp-project/blob/e59ff114b69002f4d00e14c2cc81f53cf734748a/src/DisjointSet.v#L130-L134

https://github.com/mbovel/itp-project/blob/e59ff114b69002f4d00e14c2cc81f53cf734748a/src/DisjointSet.v#L196-L200

https://github.com/mbovel/itp-project/blob/e59ff114b69002f4d00e14c2cc81f53cf734748a/src/DisjointSet.v#L202-L207

https://github.com/mbovel/itp-project/blob/e59ff114b69002f4d00e14c2cc81f53cf734748a/src/DisjointSet.v#L292-L293

https://github.com/mbovel/itp-project/blob/e59ff114b69002f4d00e14c2cc81f53cf734748a/src/DisjointSet.v#L311-L315

## Top-down proof walkthrough

Main theorem:

https://github.com/mbovel/itp-project/blob/2ae3a5bbb5bbe0a32ce586120b9711f65079082a/src/DisjointSet.v#L596-L602


Both are proved by induction on the axioms list.

### Theory implies implementation

https://github.com/mbovel/itp-project/blob/2ae3a5bbb5bbe0a32ce586120b9711f65079082a/src/DisjointSet.v#L487-L489

How can make use of the induction hypothesis?

**Main idea:** backward cases analysis theorem to decompose the goal into smaller goals:

https://github.com/mbovel/itp-project/blob/19bc79277f4c91179d64c95a583306273d02a790/src/Equivalence.v#L75-L82

**Case 1**: `x` already equal to `y` before adding the new axiom.

https://github.com/mbovel/itp-project/blob/19bc79277f4c91179d64c95a583306273d02a790/src/DisjointSet.v#L421-L423

**Case 2**: we add an axiom `(z, w)` and before `eq axms z x` and `eq axms w y`.

https://github.com/mbovel/itp-project/blob/19bc79277f4c91179d64c95a583306273d02a790/src/DisjointSet.v#L376-L380

which proves that `union` indeed merges equivalence classes.

**Case 3**: we add an axiom `(z, w)` and before `eq axms w x` and `eq axms z y`.

Basically prove that it's okay to swap `z` and  `w` in the axiom pair using `union_mono` and `union_correct`.

### Implementation implies theory

https://github.com/mbovel/itp-project/blob/2ae3a5bbb5bbe0a32ce586120b9711f65079082a/src/DisjointSet.v#L552-L554

**Main idea:** similar to the previous theorem, we use backward cases analysis to decompose the goal into smaller goals, in the other direction.

https://github.com/mbovel/itp-project/blob/7aa2767baa50a1303f9c5a28f7d697b1ae24c0d7/src/Equivalence.v#L75-L82

Then we proceed brutally by analysing all possible cases:

https://github.com/mbovel/itp-project/blob/7aa2767baa50a1303f9c5a28f7d697b1ae24c0d7/src/DisjointSet.v#L567-L571

Three lemmas to help:

https://github.com/mbovel/itp-project/blob/7aa2767baa50a1303f9c5a28f7d697b1ae24c0d7/src/DisjointSet.v#L521-L525

https://github.com/mbovel/itp-project/blob/7aa2767baa50a1303f9c5a28f7d697b1ae24c0d7/src/DisjointSet.v#L538-L541

https://github.com/mbovel/itp-project/blob/7aa2767baa50a1303f9c5a28f7d697b1ae24c0d7/src/DisjointSet.v#L545-L548

## Current state

```
-------------------------------------------------------------------------------
Language                     files          blank        comment           code
-------------------------------------------------------------------------------
Coq                              2             68             39            596
```

Almost finished the disjoint-set implementation and proof.

## Next steps

Finish the disjoint-set proof.

Still hope to include some more, about congruence closure and normalization.

:)
