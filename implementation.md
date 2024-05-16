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

## Top-level proof walkthrough

https://github.com/mbovel/itp-project/blob/2ae3a5bbb5bbe0a32ce586120b9711f65079082a/src/DisjointSet.v#L596-L602

### Left to right: theory implies implementation

https://github.com/mbovel/itp-project/blob/2ae3a5bbb5bbe0a32ce586120b9711f65079082a/src/DisjointSet.v#L552-L554

## Right to left: implementation implies theory

https://github.com/mbovel/itp-project/blob/2ae3a5bbb5bbe0a32ce586120b9711f65079082a/src/DisjointSet.v#L487-L489
