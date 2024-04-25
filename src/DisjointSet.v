Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.Equalities.
Import List.
Import ListNotations.

Require Import Equivalence.

Module Type BOOL_EQ.
  Parameter A : Type.
  Axiom eq_dec : forall (x y : A), {x = y} + {x <> y}.
  Parameter beq : A -> A -> bool.
  Axiom beq_correct : forall x y : A, beq x y = true <-> x = y.
  Notation "x =? y" := (beq x y) (at level 70).
End BOOL_EQ.

Module StringBoolEq <: BOOL_EQ.
  Definition A := string.
  Definition eq_dec := String.string_dec.
  Definition beq := String.eqb.
  Definition beq_correct := String.eqb_eq.
End StringBoolEq.

Module Type DISJOINT_SET (Import BE : BOOL_EQ).
  Parameter D : Type.
  Parameter empty : D.
  Parameter union : D -> A -> A -> D.
  Parameter equiv : D -> A -> A -> bool.
  Axiom make_correct: forall axms x y,
    let ds := fold_left (fun ds axm => union ds (fst axm) (snd axm)) axms empty in
    eq axms x y <-> equiv ds x y = true.
End DISJOINT_SET.

Module DisjointSetList (Import BE : BOOL_EQ) <: DISJOINT_SET BE.
  Definition D := list (list A).
  Definition empty : D := [].

  Fixpoint list_beq (xs ys : list A) : bool :=
    match xs, ys with
    | [], [] => true
    | x::xs', y::ys' => beq x y && list_beq xs' ys'
    | _, _ => false
    end.

  Definition union (ds: D) (x y: A) : D :=
    let lx_opt := find (fun l => existsb (beq x) l) ds in
    let ly_opt := find (fun l => existsb (beq y) l) ds in
    match lx_opt, ly_opt with
    | Some lx, Some ly => 
      let ds' := filter (fun l => negb (list_beq lx l) && negb (list_beq ly l)) ds in
      (lx ++ ly) :: ds'
    | Some lx, None => lx :: ds
    | None, Some ly => ly :: ds
    | None, None => [x; y] :: ds
    end.
  
  Definition equiv (ds: D) (x y: A) : bool :=
    match find (fun l => existsb (beq x) l) ds, find (fun l => existsb (beq y) l) ds with
    | Some lx, Some ly => list_beq lx ly
    | _, _ => false
    end.

  Theorem make_correct: forall axms x y,
    let ds := fold_left (fun ds axm => union ds (fst axm) (snd axm)) axms empty in
    eq axms x y <-> equiv ds x y = true.
  Proof.
  Admitted.
End DisjointSetList.
