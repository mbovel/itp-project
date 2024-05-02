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
  Notation "x =? y" := (beq x y) (at level 70).
  Axiom beq_correct : forall x y : A, (x =? y) = true <-> x = y.
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
  Fixpoint make_graph (axms: list (A * A)) : D :=
    match axms with
    | [] => empty
    | (x, y)::axms' => union (make_graph axms') x y
    end.
  Axiom make_correct: forall axms x y,
    eq axms x y <-> equiv (make_graph axms) x y = true.
End DISJOINT_SET.

Module DisjointSetListList (Import BE : BOOL_EQ) <: DISJOINT_SET BE.
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

  Fixpoint make_graph (axms: list (A * A)) : D :=
    match axms with
    | [] => empty
    | (x, y)::axms' => union (make_graph axms') x y
    end.

  Theorem make_correct: forall axms x y,
    eq axms x y <-> equiv (make_graph axms) x y = true.
  Proof.
  Admitted.
End DisjointSetListList.

Compute (fst (1, 2)).
Compute (snd (1, 2)).

Module DisjointSetListPair (Import BE : BOOL_EQ) <: DISJOINT_SET BE.
  Definition D := list (A * A).
  Definition empty : D := [].

  Definition repr (ds: D) (x: A) : option A :=
    match find (fun pairr => (fst pairr) =? x) ds with
    | Some rx => Some (snd rx)
    | None => None
    end.

  Definition ensure_contains (ds: D) (x: A) : D :=
    match find (fun pairr => (fst pairr) =? x) ds with
    | Some _ => ds
    | None => (x, x) :: ds
    end.

  Definition union (ds: D) (x y: A) : D :=
    let rx_opt := repr ds x in
    let ry_opt := repr ds y in
    match rx_opt, ry_opt with
    | Some rx, Some ry => map (fun pairr => if (snd pairr) =? ry then (fst pairr, rx) else pairr) ds
    | Some rx, None => (y, rx) :: ds
    | None, Some ry => (x, ry) :: ds
    | None, None => (x, y) :: ds
    end.
  
  Definition equiv (ds: D) (x y: A) : bool :=
    let rx_opt := repr ds x in
    let ry_opt := repr ds y in
    match rx_opt, ry_opt with
    | Some rx, Some ry => rx =? ry
    | Some rx, None => rx =? y
    | None, Some ry => x =? ry
    | None, None => x =? y
    end.

  Fixpoint make_graph (axms: list (A * A)) : D :=
    match axms with
    | [] => empty
    | (x, y)::axms' => union (make_graph axms') x y
    end.

  Lemma equiv_refl: forall ds x,
    equiv ds x x = true.
  Proof.
    intros.
    unfold equiv.
    destruct (repr ds x) eqn:Heq; apply beq_correct; reflexivity.
  Qed.


  Lemma union_mono: forall ds x rx y ry z w r,
    let ds' := (union ds z w) in
    (repr ds x) = rx -> (repr ds y) = ry -> rx = ry -> rx = Some r -> (repr ds' x) = (repr ds' y).
  Proof.
    intros.
    unfold union in ds'.
    destruct (repr ds z) eqn:Heqz, (repr ds w) eqn:Heqw.
    - destruct ( r =? a0) eqn:HeqRA0.
      (* r == a0 *)
      + Search (map). admit.
      + admit.
    - destruct ( w =? x ) eqn:Heqwx.
      (* w == x*)
      + simpl. destruct ( w =? y) eqn:Heqwy.
        (* w == y*)
        ++ unfold repr. simpl. rewrite Heqwx. rewrite Heqwy. reflexivity.
        (* w != y && w == x *)
        ++ simpl. rewrite H1 in H2. apply beq_correct in Heqwx. subst. rewrite H2 in H1. rewrite H1 in Heqw. discriminate.
      (* w != x *)
      + simpl. destruct ( w =? y) eqn:Heqwy.
        (* w == y && w != x *)
        ++ rewrite beq_correct in Heqwy. subst. rewrite H1 in H2. rewrite H2 in Heqw. discriminate.
        (* w != y && w != x *)
        ++ simpl. unfold repr. simpl. rewrite Heqwx. rewrite Heqwy. subst. unfold repr in H1. simpl in H1. apply H1.
    - destruct ( z =? x ) eqn:Heqzx.
      (* z == x*)
      + simpl. destruct ( z =? y) eqn:Heqzy.
        (* z == y*)
        ++ unfold repr. simpl. rewrite Heqzx. rewrite Heqzy. reflexivity.
        (* z != y && z == x *)
        ++ simpl. rewrite H1 in H2. apply beq_correct in Heqzx. subst. rewrite H2 in H1. rewrite H1 in Heqz. discriminate.
      (* z != x *)
      + simpl. destruct ( z =? y) eqn:Heqzy.
        (* z == y && z != x *)
        ++ rewrite beq_correct in Heqzy. subst. rewrite H1 in H2. rewrite H2 in Heqz. discriminate.
        (* z != y && z != x *)
        ++ simpl. unfold repr. simpl. rewrite Heqzx. rewrite Heqzy. subst. unfold repr in H1. simpl in H1. apply H1.
    - destruct ( z =? x ) eqn:Heqzx.
      (* z == x*)
      + simpl. destruct ( z =? y) eqn:Heqzy.
        (* z == y*)
        ++ unfold repr. simpl. rewrite Heqzx. rewrite Heqzy. reflexivity.
        (* z != y && z == x *)
        ++ simpl. rewrite H1 in H2. apply beq_correct in Heqzx. subst. rewrite H2 in H1. rewrite H1 in Heqz. discriminate.
      (* z != x *)
      + simpl. destruct ( z =? y) eqn:Heqzy.
        (* z == y && z != x *)
        ++ rewrite beq_correct in Heqzy. subst. rewrite H1 in H2. rewrite H2 in Heqz. discriminate.
        (* z != y && z != x *)
        ++ simpl. unfold repr. simpl. rewrite Heqzx. rewrite Heqzy. subst. unfold repr in H1. simpl in H1. apply H1.
  Admitted.

  Lemma un: forall axms x y z w,
    equiv (make_graph axms) x y = true -> equiv (make_graph ((z, w) :: axms)) x y = true.
  Proof.
    intros.
    simpl.
    (*
    induction axms; intros.
    - unfold equiv in H. simpl in H. apply beq_correct in H. subst. apply equiv_refl.
    - simpl in *.
      destruct a as [z w].
    *)
  Qed.

  Theorem make_correct: forall axms x y,
    eq axms x y <-> equiv (make_graph axms) x y = true.
  Proof.
    induction axms; intros.
    - split; intros; unfold equiv in *; simpl in *.
      + apply eq_empty in H. subst. apply beq_correct. reflexivity.
      + apply beq_correct in H. subst. apply eq_empty. reflexivity.
    - split; intros; simpl in *.
      + destruct a as [z w].
        destruct (equiv (make_graph axms) x y) eqn:Heq.
        * 
        * 

      
  Admitted.
End DisjointSetListPair.
