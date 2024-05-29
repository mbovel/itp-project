---
title: Equivalence Closure Data Structure in Coq
author: "[Samuel Chassot](mailto:samuel.chassot@epfl.ch) @[LARA](https://epfl-lara.github.io), [EPFL](https://www.epfl.ch/fr/)<br/>[Matt Bovel](mailto:matthieu.bovel@epfl.ch) @[LAMP](https://www.epfl.ch/labs/lamp/)/[LARA](https://epfl-lara.github.io), [EPFL](https://www.epfl.ch/fr/)"
---

# Introduction

- **What?**
  - Equivalence closure data structure in Coq
  - Decision procedure for equivalent closure relations
  - Correctness proof
- **Why?**
  - Used in many applications: type systems, SMT solvers, verification, ...
  - For example, verify: `if x == y && y == z then assert(x == z)`
  - Understand automatic reasoning about equality

# Equivalence closure

- **Relation**:
  - Binary relation: $R \subseteq A \times A$
  - Define $xRy$ as $(x, y) \in R$
- **Equivalence closure**:
  - Reflexive-symmetric-transitive closure of $R$
  - $rst(R)$ is the smallest relation such as:
    - Axioms: $R \subseteq rst(R)$
    - Reflexivity: $\forall a. \; (a, a) \in rst(R)$
    - Symmetry: $\forall a, b. \; (a, b) \in rst(R) \Rightarrow (b, a) \in rst(R)$
    - Transitivity: $\forall a, b, c. \;\left((a, b) \in rst(R) \land (b, c) \in rst(R) \right) \Rightarrow (a, c) \in rst(R)$

# Equivalence closure in Coq

```coq
Inductive eq {A : Type} (axms : list (A * A)) : A -> A -> Prop :=
  | eq_axms: forall x y: A, In (x, y) axms -> eq axms x y
  | eq_refl: forall x: A, eq axms x x
  | eq_sym: forall x y: A, eq axms y x -> eq axms x y
  | eq_trans: forall x y z: A, eq axms x y -> eq axms y z -> eq axms x z.
```

# Union-find

- Existing data structure for equivalence closure
- Store $e \rightarrow parent$ mappings
- Compute representative
- Path compression for performance

# Union-find data structure implementation

```scala
/** Immutable implementation of a disjoint set data structure, based on
  * union-find without rank or path compression. */
final class DisjointSet[A](val parents: Map[A, A] = Map.empty[A, A]):
  def repr(a: A): A =
    val parent = parents.getOrElse(a, a)
    if parent == a then a else repr(parent)

  def equiv(a: A, b: A): Boolean =
    repr(a) == repr(b)

  def union(a: A, b: A): DisjointSet[A] =
    val aRepr = repr(a)
    val bRepr = repr(b)
    DisjointSet(parents + (bRepr -> aRepr))
```

# Easier-to-prove implementation

```scala
final case class DisjointSet[A](val classes: List[(A, A)]):
  def repr(a: A): A =
    classes.find(p => p._1 == a) match
      case None         => a
      case Some((_, r)) => r

  def equiv(a: A, b: A): Boolean =
    repr(a) == repr(b)

  def union(a: A, b: A): DisjointSet[A] =
    val aRepr = repr(a)
    val bRepr = repr(b)
    val gPrime = ensureRepr(ensureRepr(classes, aRepr), bRepr)
    DisjointSet(gPrime.map(p => if p._2 == bRepr then (p._1, aRepr) else p))
```

---

Helper to ensure that a value has a representative:

```scala
def ensureRepr[A](classes: List[(A, A)], a: A): List[(A, A)] =
  classes.find(p => p._1 == a) match
    case None    => (a, a) :: classes
    case Some(_) => classes
```

This avoids any other check or invariant about the existence of representatives in the list-map.

# Disjoint-set interface

```coq
Module Type DISJOINT_SET (Import BE : BOOL_EQ).
  Parameter D : Type.
  Parameter empty : D.
  Parameter union : D -> A -> A -> D.
  Parameter equiv : D -> A -> A -> bool.
  Fixpoint make_graph (axms: list (A * A)) : D :=
    match axms with
    | [] => empty
    | (x, y)::axms' => union (make_graph axms') x y
    end.
  Axiom make_correct: forall axms x y,
    eq axms x y <-> equiv (make_graph axms) x y = true.
End DISJOINT_SET.
```

# Equatable type interface

```coq
Module Type BOOL_EQ.
  Parameter A : Type.
  Axiom eq_dec : forall (x y : A), {x = y} + {x <> y}.
  Parameter beq : A -> A -> bool.
  Notation "x =? y" := (beq x y) (at level 70).
  Axiom beq_correct : forall x y : A, (x =? y) = true <-> x = y.
End BOOL_EQ.
```

<div class="fragment">

```
Module StringBoolEq <: BOOL_EQ.
  Definition A := string.
  Definition eq_dec := String.string_dec.
  Definition beq := String.eqb.
  Definition beq_correct := String.eqb_eq.
End StringBoolEq.
```

</div>

# Disjoint-set as a list of pairs

```coq
Module DisjointSetListPair (Import BE : BOOL_EQ) <: DISJOINT_SET BE.
  Definition D := list (A * A).
  Definition empty : D := [].
```

---

<div class="fragment">

```coq
  Fixpoint get (ds: D) (x: A) : option A :=
    match ds with
    | [] => None
    | (z, w)::ds' => if x =? z then Some w else get ds' x
    end.
```

</div>

<div class="fragment">

```coq
  Definition repr (ds: D) (x: A) : A :=
    match get ds x with
    | Some y => y
    | None => x
    end.
```

</div>

<div class="fragment">

```coq
  Definition equiv (ds: D) (x y: A) : bool :=
    (repr ds x) =? (repr ds y).
```

</div>

---

<div class="fragment">

```coq
  Definition ensure_repr (ds: D) (x: A) : D :=
    match get ds x with
    | Some _ => ds
    | None => (x, x) :: ds
    end.
```

</div>

<div class="fragment">

```coq
  Fixpoint replace_values (ds: D) (v1 v2: A) : D :=
    match ds with
    | [] => []
    | (x, y)::ds' => (x, if y =? v1 then v2 else y) :: replace_values ds' v1 v2
    end.
```

</div>

<div class="fragment">

```coq
  Definition union (ds: D) (x y: A) : D :=
    let xr := (repr ds x) in
    let yr := (repr ds y) in
    let ds' := (ensure_repr (ensure_repr ds xr) yr) in
    (replace_values ds' yr xr).
```

</div>

# Proof intuition

Remember, we want to prove:

```coq
Axiom make_correct: forall axms x y,
    eq axms x y <-> equiv (make_graph axms) x y = true.
```

**Technique:** we went with an induction on the axioms list for both directions.

**Main question:** how to make use of the induction hypothesis? How to relate `eq axms x y` to `eq ((z, w) :: axms) x y`?

---

**Main intuition:** if we have `eq ((w, z) :: axms) x y` it's either that

1. `x` and `y` were already equivalent with `axms`,
2. or `x` was equivalent to `z` and `y` was equivalent to `w` with `axms`,
3. or `x` was equivalent to `w` and `y` was equivalent to `z` with `axms`.

<img src="res/EPFL-Coq-equivalence-classes.svg" height="444px" style="margin: 0 auto; display: block;">

---

Written otherwise:

```coq
Lemma eq_nonempty: forall {A} (x y z w: A) (axms: list (A * A)),
   (
     (eq axms x y)
     \/ (eq axms x z /\ eq axms y w)
     \/ (eq axms x w /\ eq axms y z)
   )
   <-> eq ((z, w) :: axms) x y.
```

