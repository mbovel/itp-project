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

## Specification

We start with an inductive definition of equivalence parametrized by a relation `R` represented as a `list (A * A)` of pairs of elements of type `A`:

```coq
Inductive eq {A : Type} (axms : list (A * A)) : A -> A -> Prop :=
  | eq_axms: forall x y: A, In (x, y) axms -> eq axms x y
  | eq_refl: forall x: A, eq axms x x
  | eq_sym: forall x y: A, eq axms y x -> eq axms x y
  | eq_trans: forall x y z: A, eq axms x y -> eq axms y z -> eq axms x z.
```

This definition represents the reflexive-symmetric-transitive closure (or equivalence closure) of the relation `R`. This gives the smallest equivalence relation that contains `R`.

This inductive definition is used as a specification for the equivalence relation data structure that we implement.

### Implementation

#### Scala candidates

We explored three different implementations of equivalence closure in Scala before implementing them in Coq. We present them here for reference:

1. Map from each element to its parent, corresponding to union-find data structure without rand or path compression:

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

    In this version, the representative of an element is either itself if its parent is itself, or the representative of its parent. If the element is not in the map, it is its own representative.

    Two elements are equivalent if their representatives are the same.

    Inserting a new equivalence between two elements `a` and `b` in the relation is done by adding a new pair to the map, mapping the parent of `b` to the parent of `a`.

2. Map from each element to its equivalence class.

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

    In this version, the representative of an element is the representative of its equivalence class, which is the first element of the list representing the classes. If the element is not in the map, it is its own representative.

    Two elements are equivalent if their representatives are the same.

    Inserting a new equivalence between two elements `a` and `b` in the relation is done by creating a new list for the new class, which is the concatenation of the lists of the classes of `a` and `b`. Then, the map is updated to map all elements of the new class to this list.

3. List of list where each list is an equivalence class.

    ```scala
    final case class DisjointSet[A](val classes: List[List[A]]):
      def union(a: A, b: A): DisjointSet[A] =
        val aClass = findEqClass(a).getOrElse(List(a))
        val bClass = findEqClass(b).getOrElse(List(b))
        if aClass == bClass then DisjointSet(classes)
        else
          val newClasses =
            (aClass ++ bClass) :: classes.filterNot(c => c == aClass || c == bClass)
          DisjointSet(newClasses)

      def find(a: A): A = findEqClass(a).getOrElse(List(a)).head

      private def findEqClass(a: A): Option[List[A]] =
        classes.find(_.contains(a))

      def equiv(a: A, b: A): Boolean =
        find(a) == find(b)
    ```

    In this version, the representative of an element is the first element of the list (i.e. class) containing this element. If no class contains the element, the element is its own representative.

    Two elements are equivalent if their representatives are the same.

    Inserting a new equivalence between two elements `a` and `b` in the relation is done by first checking whether the two classes are in fact the same class: if that is the case, the structure is left unchanged; otherwise, a new class is created by concatenating the two classes and removing the old classes from the list of classes.

4. List of pairs, effectively mapping each element to its representative.

    ```scala
    final case class DisjointSet[A](val classes: List[(A, A)]):
      def union(a: A, b: A): DisjointSet[A] =
        val aRepr = find(a)
        val bRepr = find(b)
        DisjointSet(
          ensureRepr(aRepr, ensureRepr(bRepr, classes)).map(p =>
            if p._2 == bRepr then (p._1, aRepr) else p
          )
        )

      def ensureRepr(a: A, classes: List[(A, A)]): List[(A, A)] =
        if (classes.find(p => p._1 == a).isDefined) classes
        else (a, a) :: classes

      def find(a: A): A = classes.find(p => p._1 == a).getOrElse((a, a))._2

      def equiv(a: A, b: A): Boolean =
        find(a) == find(b)
    ```

    In this version, the representative of an element is the second element of the pair containing this element. If no pair contains the element, the element is its own representative.

    Two elements are equivalent if their representatives are the same.

    Inserting a new equivalence between two elements `a` and `b` in the relation is done by first finding the representatives of `a` and `b`, then ensuring that they are in the list of pairs. Finally, the list of pairs is updated to change the representative of all elements that had the same representative as `b` to the have the representative of `a` instead.

    It is interesting to note that this version is similar to the version 1, but differs in the way that finding the representative is now a constant time operation, that is not defined recursively. The cost is transferred to the `union` operation that now needs to update all pairs that have the same representative as `b`, i.e., elements that are members the classes of equivalence of `b`.

#### Coq implementation

##### Interface

We first define a Coq `Module` representing the disjoint-set interface:

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

This module defines a type `D` for the disjoint-set data structure that represents the equivalence closure of an underlying implicit relation `R`, an empty disjoint-set `empty`, a union operation `union` that adds a new pair `(a, b)` to the relation `R`, and an equivalence check `equiv`. The `make_graph` function builds a disjoint-set data structure from a list of pairs of elements. The `make_correct` axiom states that the equivalence relation represented by the disjoint-set data structure is equivalent to the equivalence closure of the relation `R` represented by the list of pairs. This `make_correct` axiom is the main theorem to prove in the project.

This disjoint-set interface is generic in the type of elements it contains. An implementation of `BOOL_EQ` for that type is required to be able to use the data structure. The `BOOL_EQ` module provides a boolean equality function for the type `A`, along with a proof that this boolean equality is equivalent to the structural equality used by Coq:

```coq
Module Type BOOL_EQ.
  Parameter A : Type.
  Axiom eq_dec : forall (x y : A), {x = y} + {x <> y}.
  Parameter beq : A -> A -> bool.
  Notation "x =? y" := (beq x y) (at level 70).
  Axiom beq_correct : forall x y : A, (x =? y) = true <-> x = y.
End BOOL_EQ.
```

Here is a simple implementation of `BOOL_EQ` for the `string` type as an example:

```coq
Module StringBoolEq <: BOOL_EQ.
  Definition A := string.
  Definition eq_dec := String.string_dec.
  Definition beq := String.eqb.
  Definition beq_correct := String.eqb_eq.
End StringBoolEq.
```

##### Implementation as a list of pairs

We implemented the fourth representation described by the Scala candidates in Coq, i.e., the implementation based on a list of pairs mapping each element to its representative. We used this particular representation as it was the most practical to work with, while remaining an efficient implementation. In the Coq implementation, the list of pairs is contrained to be a map, i.e., a list of pairs `(A * A)` with no two pairs with the same first element.

We implemented it as of as another `Module` in Coq, implementing the interface described above:

```coq
Module DisjointSetListPair (Import BE : BOOL_EQ) <: DISJOINT_SET BE.
  Definition D := list (A * A).
  Definition empty : D := [].
```

The `replace_values` function implements the `map` application in the Scala implementation, replacing all values `v1` by `v2` appearing in the second position of a pair in the list:

```coq
Fixpoint replace_values (ds: D) (v1 v2: A) : D :=
    match ds with
    | [] => []
    | (x, y)::ds' => (x, if y =? v1 then v2 else y) :: replace_values ds' v1 v2
    end.
```

We use this custom implementation instead of a call to `map` for better control over the function and the proof that work with and on it.

We then define the `repr` function returning the representative of an element in the disjoint-set data structure and the `ensure_repr` function that ensures that an element is in the disjoint-set data structure, i.e., the list contains a pair with the element as the first element:

```coq
Definition repr (ds: D) (x: A) : A :=
  match get ds x with
  | Some y => y
  | None => x
  end.

Definition ensure_repr (ds: D) (x: A) : D :=
  match get ds x with
  | Some _ => ds
  | None => (x, x) :: ds
  end.
```

We then can implement the `equiv` function that checks whether two elements are equivalent in the disjoint-set data structure:

```coq
Definition equiv (ds: D) (x y: A) : bool :=
  (repr ds x) =? (repr ds y).
```

The `union` function is implemented as in the Scala version, but with the `replace_values` function instead of a call to `map`:

```coq
Definition union (ds: D) (x y: A) : D :=
  let xr := (repr ds x) in
  let yr := (repr ds y) in
  let ds' := (ensure_repr (ensure_repr ds xr) yr) in
  (replace_values ds' yr xr).
```

Finally, we define the `make_graph` function that builds a disjoint-set data structure from a list of pairs of elements:

```coq
Fixpoint make_graph (axms: list (A * A)) : D :=
  match axms with
  | [] => empty
  | (x, y)::axms' => union (make_graph axms') x y
  end.
```

`make_graph` calls `union` for each pair in the list of pairs, building the disjoint-set data structure incrementally.

#### Runtime complexity analysis

We analyse briefly the difference in runtime complexity of the algoirthm implemented by the disjoint-set data structure:

- Equivalence check: the worst case is `O(N)` where `N` is the number of pairs in the list, as we need to traverse the list to find the representative of each element. This could go down to `O(1)` with a smarter implementation of the map structure. The linear cost comes from the representation as a list rather than being inherent to the algorithm.
- Union: the worst case is `O(N)` where `N` is the number of pairs in the list, as we need to traverse the list to find the representative of each element. This could go down to `O(M)` where `M` is the size of the largest equivalence class, with a smarter implementation of the map structure. Indeed, when adding a new axiom `(w, z)`, the representative of all elements in the class of `z` need to be updated to the representative of `w`.

### Proof

As stated in the previous section, the main theorem to prove is the following:

```coq
Axiom make_correct: forall axms x y,
    eq axms x y <-> equiv (make_graph axms) x y = true.
```

which states that two elements are equivalent according to the disjoint-set structure for the relation `R` if and only if they are equivalent according in the equivalence closure of `R`. `R` is represented by a list of axioms `axms`. This list is a list of pairs `(x, y)`, meaning that `x` and `y` are equivalent in the relation `R`.

The proof of this theorem is done by induction on the list of axioms `axms`. The base case is trivial, as the empty list of axioms corresponds to the empty relation, and the disjoint-set data structure built from it is also empty, implying that no different elements are equivalent.

For the inductive case however, we need a way to reason about the equivalence of two elements `x` and `y` in the disjoint-set data structure built from a list of axioms with an additional axiom `(w, z)`. Exposed differently, we need to reason about what happens when we add an axiom `(w, z)` to a list of axioms `axms'` and build the disjoint-set data structure from it. 

Formally, this boils down to analysing what `eq (w, z) :: axms' x y` means with respect to `eq axms' x y`. This is one of the pivotal lemmas of the proof.

The lemma is the following:

```coq
  (
     (eq axms x y)
     \/ (eq axms x z /\ eq axms y w)
     \/ (eq axms x w /\ eq axms y z)
  )
    <-> eq ((z, w) :: axms) x y.
```

A careful case analysis shows that there are three cases to consider, that we will explain with the help of a diagram:

<!-- The following line adds the diagram svg file -->
![Diagram](./res/EPFL-Coq-equivalence-classes.svg)

Let us detail the three cases:

1. `x` and `y` are already equivalent in the relation `R` represented by `axms`. In this case, adding the axiom `(z, w)` does not change the equivalence of `x` and `y` in the relation `R` represented by `(z, w) :: axms`.

2. `x` and `y` are in two different classes in the relation `R` represented by `axms`, and adding a new axiom `(w, z)` acutally merges the two classes, because `w` is in the same class as `x` and `z` is in the same class as `y`.

3. This is the same situation as 2., but with `w` and `z` swapped. This case is symmetric to the previous one.

These are the three possible cases leading to `x` and `y` being equivalent under the relation `R` represented by `(z, w) :: axms`. We use this case analysis to prove the inductive case of our proof by induction on the list of axioms.

## References

- [Formalization of a persistent union-find data structure in Coq](https://www.lri.fr/~filliatr/puf/)
- [A Simple, Probably-Not-Exp-Time Disjoint Set in Coq](https://www.philipzucker.com/simple-coq-union-find/)
- [Techniques for Program Verification, Nelson, 1981](https://people.eecs.berkeley.edu/~necula/Papers/nelson-thesis.pdf): original paper on congruent closure algorithm.
- [Intro to EGraphs, Colab](https://colab.research.google.com/drive/1tNOQijJqe5tw-Pk9iqd6HHb2abC5aRid): nice introduction to EGraphs.
- [EGG (EGraphs Good)](https://egraphs-good.github.io): combining EGraphs and equality saturation to implement optimizers.
- [Proof-producing Congruence Closure](https://www.cs.upc.edu/~oliveras/rta05.pdf)
- [Project: congruence closure algorithm in Coq using dependent types](https://github.com/knuthingmuch/congruence-closure): similar course project from 2019.
