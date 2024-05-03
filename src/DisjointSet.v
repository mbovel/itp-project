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


Module DisjointSetListPair (Import BE : BOOL_EQ) <: DISJOINT_SET BE.
  Definition D := list (A * A).
  Definition empty : D := [].

  Fixpoint get (ds: D) (x: A) : option A :=
    match ds with
    | [] => None
    | (z, w)::ds' => if x =? z then Some w else get ds' x
    end.

  Fixpoint is_map (ds: D) : Prop :=
    match ds with
    | [] => True
    | (x, y)::ds' => get ds' x = None /\ is_map ds'
    end.

  Lemma get_in: forall ds x y,
    get ds x = Some y -> In (x, y) ds.
  Proof.
    induction ds.
    - discriminate.
    - destruct a as [z w]; intros; simpl in *.
      destruct (x =? z) eqn:Heq.
      + apply beq_correct in Heq. left. congruence.
      + right. apply IHds. assumption.
  Qed.

  Lemma beq_refl: forall x,
    x =? x = true.
  Proof. intros. apply beq_correct. reflexivity. Qed.

  Lemma in_get: forall ds x y,
    is_map ds -> In (x, y) ds -> get ds x = Some y.
  Proof.
    induction ds.
    - intros. contradiction.
    - destruct a as [z w]; intros; simpl in *.
      destruct H0.
      + injection H0 as H0 H1. subst. rewrite beq_refl. reflexivity.
      + destruct H as [H H'].
        destruct (x =? z) eqn:Heq.
        * apply beq_correct in Heq.
          subst.
          pose proof (IHds z y H' H0) as IH.
          rewrite H in IH.
          discriminate.
        * apply IHds; try assumption.
  Qed.

  Fixpoint replace_values (ds: D) (v1 v2: A) : D :=
    match ds with
    | [] => []
    | (x, y)::ds' => (x, if y =? v1 then v2 else y) :: replace_values ds' v1 v2
    end.

  Lemma nbeq_correct: forall x y,
    x =? y = false <-> x <> y.
  Proof.
    intros. split; intros.
    - intros H1. apply beq_correct in H1. rewrite H1 in H. discriminate.
    - destruct (x =? y) eqn:Heq.
      + apply beq_correct in Heq. contradiction.
      + reflexivity.
  Qed.

  Lemma replace_values_correct: forall ds k v1 v2,
    get ds k = Some v1 ->
    get (replace_values ds v1 v2) k = Some v2.
  Proof.
    induction ds.
    - discriminate.
    - destruct a as [k0 v0].
      intros.
      simpl.
      destruct (k =? k0) eqn:Hk.
      + apply beq_correct in Hk. subst.
        destruct (v0 =? v1) eqn:Hv.
        * apply beq_correct in Hv. subst. reflexivity.
        * apply nbeq_correct in Hv. simpl in H. rewrite beq_refl in H. congruence.
      + simpl in H. rewrite Hk in H. apply IHds. assumption.
  Qed.

  Lemma replace_values_correct_neq: forall ds k v v1 v2,
    get ds k = Some v -> v <> v1 ->
    get (replace_values ds v1 v2) k = Some v.
  Proof.
    induction ds.
    - discriminate.
    - destruct a as [k0 v0].
      intros.
      simpl in *.
      destruct (k =? k0) eqn:Hk.
      + rewrite beq_correct in *. subst.
        injection H as H. subst.
        destruct (v =? v1) eqn:Hv.
        * apply beq_correct in Hv. contradiction.
        * reflexivity.
      + apply IHds; assumption.
  Qed.

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

  Lemma ensure_repr_exists: forall ds x,
    exists rx, get (ensure_repr ds x) x = Some rx.
  Proof.
    intros.
    unfold ensure_repr.
    destruct (get ds x) eqn:Heq.
    - exists a. assumption.
    - exists x. simpl. rewrite beq_refl. reflexivity.
  Qed.

  Lemma repr_head: forall ds x y,
    repr ((x, y) :: ds) x = y.
  Proof. intros. unfold repr, get. rewrite beq_refl. reflexivity. Qed.

  (*
  Lemma ensure_repr_correct: forall ds x rx,
    repr ds x = rx -> repr (ensure_repr ds x) x = rx.
  Proof.
    intros.
    unfold ensure_repr.
    destruct (get ds x) eqn:Heq.
    - assumption.
    - unfold repr in H. rewrite Heq in H. simpl in H. subst. apply repr_head.
  Qed.
  *)

  Lemma ensure_repr_mono: forall ds x rx y,
    get ds x = Some rx -> get (ensure_repr ds y) x = Some rx.
  Proof.
    intros.
    unfold ensure_repr.
    destruct (get ds y) eqn:Heq.
    - assumption.
    - simpl.
      destruct (x =? y) eqn:Heqxy.
      + apply beq_correct in Heqxy. subst. rewrite H in Heq. discriminate.
      + assumption.
  Qed.

  Lemma ensure_repr_preserve: forall ds x y rx,
    repr ds x = rx -> repr (ensure_repr ds y) x = rx.
  Proof.
    intros.
    unfold ensure_repr.
    destruct (get ds y) eqn:Heq.
    - assumption.
    - destruct (eq_dec x y).
      + subst. rewrite repr_head. unfold repr. rewrite Heq. reflexivity.
      + unfold repr, get. apply nbeq_correct in n. rewrite n. assumption.
  Qed.

  Lemma ensure_repr_get: forall ds x rx,
    repr ds x = rx -> get (ensure_repr ds x) x = Some rx.
  Proof.
    intros.
    unfold repr in *.
    destruct (get ds x) eqn:Hx; subst.
    - auto using ensure_repr_mono.
    - unfold ensure_repr. rewrite Hx. simpl. rewrite beq_refl. reflexivity.
  Qed.

  Lemma ensure_repr_get_2: forall ds x rx,
    repr ds x = rx -> get (ensure_repr ds rx) x = Some rx.
  Proof.
    intros.
    unfold repr in *.
    destruct (get ds x) eqn:Hx; subst.
    - auto using ensure_repr_mono.
    - unfold ensure_repr. rewrite Hx. simpl. rewrite beq_refl. reflexivity.
  Qed.
  
  Definition equiv (ds: D) (x y: A) : bool :=
    (repr ds x) =? (repr ds y).

  Lemma equiv_refl: forall ds x,
    equiv ds x x = true.
  Proof.
    intros.
    unfold equiv.
    destruct (get ds x) eqn:Heq; apply beq_correct; reflexivity.
  Qed.
  
  Definition union (ds: D) (x y: A) : D :=
    let xr := (repr ds x) in
    let yr := (repr ds y) in
    let ds' := (ensure_repr (ensure_repr ds xr) yr) in
    (replace_values ds' yr xr).

  Lemma union_mono: forall ds x y w z,
    equiv ds x y = true -> equiv (union ds w z) x y = true.
  Proof.
  Admitted.

  Lemma union_correct_1: forall ds x xr y yr,
    (get ds x) = Some xr ->
    (get ds y) = Some yr ->
    (equiv (replace_values ds yr xr) x y = true).
  Proof.
    intros.
    unfold equiv in *.
    rewrite beq_correct in *.
    unfold repr.
    pose proof (replace_values_correct ds y yr xr H0) as H1.
    rewrite H1.
    destruct (eq_dec xr yr) as [Heq | Hneq].
    - subst. rewrite replace_values_correct.
      + reflexivity.
      + assumption.
    - pose proof (replace_values_correct_neq ds x xr yr xr H Hneq) as H2.
      rewrite H2. reflexivity.
  Qed.

  Theorem union_correct : forall ds x x' y y',
    (equiv ds x x' = true) ->
    (equiv ds y y' = true) ->
    (equiv (union ds x y) x' y' = true).
  Proof.
    intros.
    unfold equiv in H, H0.
    unfold union.
    rewrite beq_correct in *.
    remember (ensure_repr (ensure_repr ds (repr ds x)) (repr ds y)) as ds'.

    (* H2 : get ds' x' = Some (repr ds x') *)
    pose proof (ensure_repr_get_2 ds x' (repr ds x) (symmetry H)) as H1.
    pose proof (ensure_repr_mono (ensure_repr ds (repr ds x)) x' (repr ds x) (repr ds y) H1) as H2.
    rewrite <- Heqds' in H2.
    clear H H1.

    (* H4 : get ds' y' = Some (repr ds y') *)
    pose proof (ensure_repr_preserve ds y' (repr ds x) (repr ds y) (symmetry H0)) as H3.
    pose proof (ensure_repr_get_2 (ensure_repr ds (repr ds x)) y' (repr ds y) H3) as H4.
    rewrite <- Heqds' in H4.
    clear H0 H3.

    apply union_correct_1; assumption.
  Qed.

  Fixpoint make_graph (axms: list (A * A)) : D :=
    match axms with
    | [] => empty
    | (x, y)::axms' => union (make_graph axms') x y
    end.
  
  Lemma make_correct_left: forall axms x y,
    eq axms x y -> equiv (make_graph axms) x y = true.
  Proof.
    induction axms; intros.
    - apply eq_empty in H.
      subst.
      unfold make_graph, equiv, repr, empty, get.
      apply beq_refl.
    - destruct a as [z w].
      apply eq_nonempty_inverse in H.
      destruct H.
      + apply IHaxms in H.
        apply union_mono.
        assumption.
      + destruct H.
        * destruct H as [H1 H2].
          apply IHaxms in H1, H2.
          apply union_correct; assumption.
        * destruct H as [H1 H2].
          apply IHaxms in H1, H2.
          apply union_correct; fold make_graph.
          admit.
  Admitted.
      
  Lemma make_correct_right: forall axms x y,
    equiv (make_graph axms) x y = true -> eq axms x y.
  Proof.
    induction axms; intros.
    - apply eq_empty.
      unfold make_graph, equiv, repr, empty, get in H.
      rewrite beq_correct in H.
      assumption.
    - destruct a as [z w].
      simpl in H.
      admit.
  Admitted.

  Theorem make_correct: forall axms x y,
    eq axms x y <-> equiv (make_graph axms) x y = true.
  Proof.
    intros. split.
    - apply make_correct_left.
    - apply make_correct_right.
  Qed.
End DisjointSetListPair.
