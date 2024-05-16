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

Tried with types classes first: https://github.com/mbovel/itp-project/pull/3/files.

Then came back to modules: https://github.com/mbovel/itp-project/pull/4/files. Easier to work with.

## Main theorem

https://github.com/mbovel/itp-project/blob/7bc0a61bfe645bbe60b34dbe0152f6850ac5f708/src/Equivalence.v#L5-L9

https://github.com/mbovel/itp-project/blob/7bc0a61bfe645bbe60b34dbe0152f6850ac5f708/src/DisjointSet.v#L25-L37
