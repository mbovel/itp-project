---
title: Equivalence Closure Data Structure in Coq
author: "[Samuel Chassot](mailto:samuel.chassot@epfl.ch) @[LARA](https://epfl-lara.github.io), [EPFL](https://www.epfl.ch/fr/)<br/>[Matt Bovel](mailto:matthieu.bovel@epfl.ch) @[LAMP](https://www.epfl.ch/labs/lamp/)/[LARA](https://epfl-lara.github.io), [EPFL](https://www.epfl.ch/fr/)"
---

# Scala code example

```scala
final class DisjointSet[A](val parents: Map[A, A] = Map.empty[A, A]):
  def union(a: A, b: A): DisjointSet[A] =
    val aRepr = find(a)
    val bRepr = find(b)
    DisjointSet(parents + (bRepr -> aRepr))

  @tailrec
  def find(a: A): A =
    val repr = parents.getOrElse(a, a)
    if repr == a then a else find(repr)

  def equiv(a: A, b: A): Boolean =
    find(a) == find(b)
```

# Coq code example

```coq
Module Type BOOL_EQ.
  Parameter A : Type.
  Axiom eq_dec : forall (x y : A), {x = y} + {x <> y}.
  Parameter beq : A -> A -> bool.
  Notation "x =? y" := (beq x y) (at level 70).
  Axiom beq_correct : forall x y : A, (x =? y) = true <-> x = y.
End BOOL_EQ.
```
