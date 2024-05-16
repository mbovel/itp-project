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

In Coq, we tried 3. first, but it was too cumbersome to work with. We then switched to 4. and it is still cumbersome.

## Coq structure

Equality axiomatisation:

https://github.com/mbovel/itp-project/blob/7bc0a61bfe645bbe60b34dbe0152f6850ac5f708/src/Equivalence.v#L5-L9

Tried with types classes first:

https://github.com/mbovel/itp-project/blob/d738ba3a33debc28b965aa1278d682d609a33de3/src/DisjointSet.v#L8-L58

Then came back to modules:

https://github.com/mbovel/itp-project/blob/0345f50283ee9a9fe85e6d399b44540ea1361887/src/DisjointSet.v#L10-L35

## Main theorem

