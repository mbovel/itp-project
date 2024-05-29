---
title: Disjoint Set Implementation in Coq
author: "[Samuel Chassot](mailto:samuel.chassot@epfl.ch) @[LARA](https://epfl-lara.github.io), [EPFL](https://www.epfl.ch/fr/)<br/>[Matt Bovel](mailto:matthieu.bovel@epfl.ch) @[LAMP](https://www.epfl.ch/labs/lamp/)/[LARA](https://epfl-lara.github.io), [EPFL](https://www.epfl.ch/fr/)"
---

# What we've done

We implemented a *disjoint set* data structure in Coq.

We proved that it can be used as a decision procedure for the *equivalence closure* of a relation.

# Equivalence closure definition


Let $R \subseteq A \times A$ be a binary relation.

We define $rst(R)$ its *reflexive-symmetric-transitive closure*—or *equivalence closure*—<br/>as the smallest relation such that:

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

# Motivation

Reasoning about equality is useful for many applications: type systems, SMT solvers, verification, etc.

For example:

```scala
if x == y && y == z then
  assert(x == z) // Verify that this always holds
```

<div class="fragment">

or:

```scala
if x == y && y == z then
  val v: (Int with v == x) = z // Verify that v == z -> v == x in this context
```

</div>

# Union-find data structure

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

**Technique:** induction on the axioms list for both directions.

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

<div class="fragment">

And the other direction:

```coq
Lemma eq_nonempty_inverse: forall {A} (x y z w: A) (axms: list (A * A)),
   eq ((z, w) :: axms) x y
   -> (
     (eq axms x y)
     \/ (eq axms z x /\ eq axms w y)
     \/ (eq axms w x /\ eq axms z y)
   ).
```

</div>

# From theory to practice

```coq
Lemma make_correct_left: forall axms x y,
  eq axms x y -> equiv (make_graph axms) x y = true.
Proof.
  induction axms; intros.
  - ...
  - destruct a as [z w].
    (* IH: forall x y : A, eq axms x y -> equiv (make_graph axms) x y = true *)
    (* H: eq ((z, w) :: axms) x y *)
    (* Goal: equiv (make_graph ((z, w) :: axms)) x y = true *)
    apply eq_nonempty_inverse in H.
    destruct H.
    + (* x was already equivlent to y in axms *)
      (* H: eq axms x y *)
      apply IHaxms in H.
      (* H: equiv (make_graph axms) x y = true *)
      apply union_mono.
      assumption.
    + destruct H.
      * (* x was equivalent to z and y was equivalent to w in axms *)
        destruct H as [H1 H2].
        (* H1: eq axms x z *)
        (* H2: eq axms w y *)
        apply IHaxms in H1, H2.
        (* H1: equiv (make_graph axms) z x = true *)
        (* H2: equiv (make_graph axms) w y = true *)
        apply union_correct; assumption.
      * (* x was equivalent to z and y was equivalent to w in axms *)
        destruct H as [H1 H2].
        (* H1: eq axms x x *)
        (* H2: eq axms z y *)
        apply IHaxms in H1, H2.
        ...
```

---

Intermediate lemmas:

```coq
Theorem union_correct: forall ds w x z y,
  (equiv ds w x = true) ->
  (equiv ds z y = true) ->
  (equiv (union ds w z) x y = true).
Proof.
  intros. unfold union. unfold equiv in H, H0. beq_to_eq.
  name_term (ensure_repr (ensure_repr ds (repr ds w)) (repr ds z)) ds'.
  assert (get ds' x = Some (repr ds w)). { eauto using ensure_repr_get, ensure_repr_mono. }
  assert (get ds' y = Some (repr ds z)). { eauto using ensure_repr_get, ensure_repr_preserve. }
  apply union_correct_1; assumption.
Qed.
```

<div class="fragment">

```coq
Lemma union_correct_1: forall ds x xr y yr,
  (get ds x) = Some xr ->
  (get ds y) = Some yr ->
  (equiv (replace_values ds yr xr) x y = true).
```

</div>

---

```coq
Lemma union_mono: forall ds x y w z,
  equiv ds x y = true -> equiv (union ds w z) x y = true.
Proof.
  intros. 
  unfold equiv in *. 
  apply beq_correct. rewrite beq_correct in H. 
  remember (repr ds y) as yr.
  remember (repr ds x) as xr.
  remember (repr ds z) as zr.
  remember (repr ds w) as wr.
  destruct (xr =? zr) eqn:Heq.
  + (* In this case, the representant of x and y will change to become wr, but still the same *)
    ...
  + (* In this case, the representant of x and y will not change *)
    ...
```

# From practice to theory

```coq
Lemma make_correct_right: forall axms x y,
  equiv (make_graph axms) x y = true -> eq axms x y.
Proof.
  induction axms; intros.
  - ...
  - destruct a as [z w].
    (* IH: forall x y : A, equiv (make_graph axms) x y = true -> eq axms x y *)
    (* H : equiv (make_graph ((z, w) :: axms)) x y = true *)
    (* Goal: eq ((z, w) :: axms) x y *)
    simpl in H.
    apply eq_nonempty.
    (* Goal: eq axms x y \/ eq axms x z /\ eq axms y w \/ eq axms x w /\ eq axms y z *)
    destruct (equiv (make_graph axms) x y) eqn:Hxy.
    + left. apply IHaxms. assumption.
    + remember (make_graph axms) as ds.
      assert (forall x y : A, repr ds x = repr ds y -> eq axms x y) as IHaxms'.
      { intros. apply IHaxms. unfold equiv. beq_to_eq. assumption. }
      destruct (equiv ds x w) eqn:Hxw, (equiv ds y w) eqn:Hyw; unfold equiv in *; beq_to_eq.
      * (* x and y are already equivalent in ds *)
        assert (repr ds x = repr ds y) by congruence.
        left. apply IHaxms. beq_to_eq. assumption.
      * (* repr of x change, repr of y stays the same *)
        pose proof (union_repr_change ds x w z Hxw) as H1.
        pose proof (union_different_same_repr ds z w y Hyw) as H2.
        right. right. split; apply IHaxms'; congruence.
      * (* repr of x stays the same, repr of y change *)
        pose proof (union_different_same_repr ds z w x Hxw) as H2.
        pose proof (union_repr_change ds y w z Hyw) as H1.
        right. left. split; apply IHaxms'; congruence.
      * (* repr of x was not w and repr of y was not w *)
        pose proof (union_different_same_repr ds z w x Hxw) as H1.
        pose proof (union_different_same_repr ds z w y Hyw) as H2.
        (* Contradiction *)
        right. congruence.
Qed.
```

---

Intermediate lemmas:

```coq
Lemma union_different_same_repr: forall ds x y z,
    repr ds z <> repr ds y -> repr (union ds x y) z = repr ds z.
```

```coq
Lemma union_repr_change: forall ds x w z,
  repr ds x = repr ds w ->
  repr (union ds z w) x = repr ds z.
Proof.
```

# Conclusion

We implemented a disjoint-set data structure in Coq and proved its correctness.
