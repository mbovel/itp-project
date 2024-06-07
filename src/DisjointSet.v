Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.Eqdep_dec.
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

(*
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
*)

Module DisjointSetListPair (Import BE : BOOL_EQ) <: DISJOINT_SET BE.
  Definition D := list (A * A).
  Definition empty : D := [].

  Fixpoint get (ds: D) (x: A) : option A :=
    match ds with
    | [] => None
    | (z, w)::ds' => if x =? z then Some w else get ds' x
    end.

  (*
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
  *)

  Fixpoint replace_values (ds: D) (v1 v2: A) : D :=
    match ds with
    | [] => []
    | (x, y)::ds' => (x, if y =? v1 then v2 else y) :: replace_values ds' v1 v2
    end.

  Lemma beq_refl: forall x,
    x =? x = true.
  Proof. intros. apply beq_correct. reflexivity. Qed.

  Lemma nbeq_correct: forall x y,
    x =? y = false <-> x <> y.
  Proof. intros. rewrite <- not_true_iff_false, beq_correct. reflexivity. Qed.

  Ltac beq_to_eq :=
    repeat match goal with
    | [ H: ?x =? ?y = true |- _ ] => rewrite beq_correct in H
    | [ H: ?x =? ?y = false |- _ ] => rewrite nbeq_correct in H
    | [ |- ?x =? ?y = true ] => rewrite beq_correct
    | [ |- ?x =? ?y = false ] => rewrite nbeq_correct
    end.

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
      + destruct (v0 =? v1) eqn:Hv; beq_to_eq; subst.
        * reflexivity.
        * simpl in H. rewrite beq_refl in H. congruence.
      + simpl in H. rewrite Hk in H. apply IHds. assumption.
  Qed.

  Lemma replace_values_correct_neq: forall ds k v v1 v2,
    get ds k = Some v ->
    v <> v1 ->
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

  Lemma replace_values_correct_neq_none: forall ds k v1 v2,
    get ds k = None ->
    get (replace_values ds v1 v2) k = None.
  Proof.
    induction ds.
    - intros. simpl. congruence.
    - destruct a as [k0 v0].
      intros.
      simpl in *.
      destruct (k =? k0) eqn:Hk.
      + discriminate.
      + apply IHds. assumption.
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

  Lemma ensure_repr_mono: forall ds x rx y,
    get ds x = Some rx -> get (ensure_repr ds y) x = Some rx.
  Proof.
    intros.
    unfold ensure_repr.
    destruct (get ds y) eqn:Hy; subst; simpl.
    - assumption.
    - destruct (x =? y) eqn:Heqxy; beq_to_eq; congruence.
  Qed.

  Lemma ensure_repr_get: forall ds x rx,
    repr ds x = rx -> get (ensure_repr ds rx) x = Some rx.
  Proof.
    intros.
    unfold repr in *.
    destruct (get ds x) eqn:Hx; subst.
    - auto using ensure_repr_mono.
    - unfold ensure_repr. rewrite Hx. simpl. rewrite beq_refl. reflexivity.
  Qed.

  Lemma ensure_repr_preserve: forall ds x y rx,
    repr ds x = rx -> repr (ensure_repr ds y) x = rx.
  Proof.
    intros.
    unfold ensure_repr.
    destruct (get ds y) eqn:Heq.
    - assumption.
    - destruct (x =? y) eqn:Heqxy.
      + beq_to_eq. subst. rewrite repr_head. unfold repr. rewrite Heq. reflexivity.
      + unfold get, repr. simpl. rewrite Heqxy. assumption.
  Qed.

  Definition equiv (ds: D) (x y: A) : bool :=
    (repr ds x) =? (repr ds y).

  Lemma equiv_refl: forall ds x,
    equiv ds x x = true.
  Proof. intros. unfold equiv in *. beq_to_eq. reflexivity. Qed.

  Lemma get_repr: forall ds x rx,
    get ds x = Some rx -> repr ds x = rx.
  Proof. intros. unfold repr. rewrite H. reflexivity. Qed.
  
  Definition union (ds: D) (x y: A) : D :=
    let xr := (repr ds x) in
    let yr := (repr ds y) in
    let ds' := (ensure_repr (ensure_repr ds xr) yr) in
    (replace_values ds' yr xr).

  Lemma beq_correct_false: forall x y,
    x =? y = false <-> x <> y.
  Proof. intros. split; intros; beq_to_eq; assumption. Qed.

  Ltac name_term term name := pose term as name; change term with name.

  Lemma union_different_same_repr: forall ds z w x,
    repr ds x <> repr ds w -> repr (union ds z w) x = repr ds x.
  Proof.
    intros.
    unfold union.
    name_term (ensure_repr (ensure_repr ds (repr ds z)) (repr ds w)) ds'.
    assert (repr ds' x = repr ds x). { eauto using ensure_repr_preserve. }
    assert (repr ds' w = repr ds w). { eauto using ensure_repr_preserve. }
    unfold repr at 1.
    destruct (get ds' x) as [rz|] eqn:Hgetz.
    - assert (repr ds x = rz). { apply get_repr in Hgetz. congruence. }
      rewrite replace_values_correct_neq with (v := rz); congruence.
    - assert (repr ds x = x). { rewrite <- H0. unfold repr. rewrite Hgetz. reflexivity. }
      rewrite replace_values_correct_neq_none; congruence.
  Qed.

  Lemma union_correct_1: forall ds x xr y yr,
    (get ds x) = Some xr ->
    (get ds y) = Some yr ->
    (equiv (replace_values ds yr xr) x y = true).
  Proof.
    intros. unfold equiv, repr in *. beq_to_eq.
    rewrite (replace_values_correct ds y yr xr H0).
    destruct (eq_dec xr yr) as [Heq | Hneq].
    - rewrite replace_values_correct; congruence.
    - rewrite (replace_values_correct_neq ds x xr yr xr H Hneq). reflexivity.
  Qed.

  Theorem union_correct: forall ds w x z y,
    (equiv ds w x = true) ->
    (equiv ds z y = true) ->
    (equiv (union ds w z) x y = true).
  Proof.
    intros.
    unfold union.
    unfold equiv in H, H0.
    beq_to_eq.
    name_term (ensure_repr (ensure_repr ds (repr ds w)) (repr ds z)) ds'.
    assert (get ds' x = Some (repr ds w)). { eauto using ensure_repr_get, ensure_repr_mono. }
    assert (get ds' y = Some (repr ds z)). { eauto using ensure_repr_get, ensure_repr_preserve. }
    apply union_correct_1; assumption.
  Qed.

  Lemma union_mono: forall ds x y w z,
    equiv ds x y = true -> equiv (union ds w z) x y = true.
  Proof.
    intros. 
    unfold equiv in *.
    destruct ((repr ds x) =? (repr ds z)) eqn:Heq; beq_to_eq.
    + (* In this case, the representatives of x and y will change to become (repr w) *)
      Ltac equiv_congruence := unfold equiv in *; beq_to_eq; congruence.
      assert (equiv ds z x = true). { equiv_congruence. }
      assert (equiv ds z y = true). { equiv_congruence. }
      assert (equiv ds w w = true). { equiv_congruence. }
      assert (equiv (union ds w z) w x = true). { auto using union_correct. }
      assert (equiv (union ds w z) w y = true). { auto using union_correct. }
      equiv_congruence.
    + (* In this case, the representatives of x and y will not change *)
      assert (repr (union ds w z) x = repr ds x). { auto using union_different_same_repr. }
      assert (repr (union ds w z) y = repr ds y). { apply union_different_same_repr. congruence. }
      congruence.
  Qed.

  Fixpoint make_graph (axms: list (A * A)) : D :=
    match axms with
    | [] => empty
    | (x, y)::axms' => union (make_graph axms') x y
    end.

  Lemma make_graph_in: forall axms x y,
    In (x, y) axms -> equiv (make_graph axms) x y = true.
  Proof.
    intros.
    induction axms.
    - contradiction.
    - destruct H.
      + subst. simpl. apply union_correct; apply equiv_refl.
      + destruct a as [z w]. simpl. apply union_mono, IHaxms. assumption.
  Qed.
  
  Lemma make_correct_left': forall axms x y,
    eq axms x y -> equiv (make_graph axms) x y = true.
  Proof.
    intros.
    induction H.
    1: apply make_graph_in. assumption.
    all: unfold equiv in *; beq_to_eq; congruence.
  Qed.

  Lemma make_correct_left: forall axms x y,
    eq axms x y -> equiv (make_graph axms) x y = true.
  Proof.
    induction axms; intros.
    - apply eq_empty in H. 
      unfold make_graph, equiv, repr, empty, get.
      beq_to_eq.
      assumption.
    - destruct a as [z w].
      (* IH: forall x y : A, eq axms x y -> equiv (make_graph axms) x y = true *)
      (* H: eq ((z, w) :: axms) x y *)
      (* Goal: equiv (make_graph ((z, w) :: axms)) x y = true *)
      apply eq_nonempty_inverse in H.
      destruct H as [H | [[H1 H2] | [H1 H2]]].
      + (* x was already equivlent to y with respect to axms *)
        (* H: eq axms x y *)
        apply IHaxms in H.
        apply union_mono. assumption.
      + (* x was equivalent to z and y was equivalent to w with respect to axms *)
        (* H1: eq axms z x *)
        (* H2: eq axms w y *)
        apply IHaxms in H1, H2.
        apply union_correct; assumption.
      + (* x was equivalent to z and y was equivalent to w with respect to axms *)
        (* H1: eq axms w x *)
        (* H2: eq axms z y *)
        apply IHaxms in H1, H2.
        unfold make_graph. fold make_graph.
        assert (equiv (make_graph axms) x w = true) as Heqxw; unfold equiv; rewrite beq_correct; unfold equiv in H1; rewrite beq_correct in H1; try congruence.
        assert (equiv (make_graph axms) y z = true) as Heqyz; unfold equiv; try rewrite beq_correct; unfold equiv in H2; rewrite beq_correct in H2; try congruence.
        pose proof (union_mono (make_graph axms) x w z w Heqxw).
        pose proof (union_mono (make_graph axms) y z z w Heqyz).
        assert (equiv (make_graph axms) w x = true) as Heqwx; unfold equiv; try rewrite beq_correct; try congruence.
        assert (equiv (make_graph axms) z y = true) as Heqzy; unfold equiv; try rewrite beq_correct; try congruence.
        pose proof (union_correct (make_graph axms) z y w x Heqzy Heqwx).
        unfold equiv in H3.
        rewrite beq_correct in H3.
        congruence.
  Qed.

  (*
  Lemma union_repr_2: forall ds x z w,
    repr ds x = repr ds z ->
    repr (union ds z w) x = repr ds z.
  Proof.
    intros.
    unfold union.
    name_term (ensure_repr (ensure_repr ds (repr ds z)) (repr ds w)) ds'.
    assert (get ds' x = Some (repr ds z)). { eauto using ensure_repr_get, ensure_repr_mono. }
    unfold repr at 1.
    destruct (eq_dec (repr ds w) (repr ds z)).
    - rewrite e, (replace_values_correct ds' x (repr ds z) (repr ds z)); auto.
    - rewrite replace_values_correct_neq with (v := repr ds z); auto.
  Qed.
  *)

  Lemma union_repr_change: forall ds x w z,
    repr ds x = repr ds w ->
    repr (union ds z w) x = repr ds z.
  Proof.
    intros.
    unfold union.
    name_term (ensure_repr (ensure_repr ds (repr ds z)) (repr ds w)) ds'.
    assert (get ds' x = Some (repr ds w)). { eauto using ensure_repr_get, ensure_repr_preserve. }
    unfold repr at 1.
    rewrite (replace_values_correct ds' x (repr ds w) (repr ds z)); auto.
  Qed.
      
  Theorem make_correct_right: forall axms x y,
    equiv (make_graph axms) x y = true -> eq axms x y.
  Proof.
    induction axms; intros.
    - apply eq_empty.
      unfold make_graph, equiv, repr, empty, get in H.
      beq_to_eq.
      assumption.
    - destruct a as [z w]. simpl in H. remember (make_graph axms) as ds.
      (* IH: forall x y : A, equiv ds x y = true -> eq axms x y *)
      (* H : equiv (union ds z w) x y = true *)
      (* Goal: eq ((z, w) :: axms) x y *)
      apply eq_nonempty.
      assert (forall x y : A, repr ds x = repr ds y -> eq axms x y) as IHaxms'.
      { intros. apply IHaxms. unfold equiv. beq_to_eq. assumption. }
      destruct (equiv ds x w) eqn:Hxw, (equiv ds y w) eqn:Hyw; unfold equiv in *; beq_to_eq.
      * (* x and y are already equivalent in ds *)
        left. apply IHaxms. beq_to_eq. congruence.
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
        left. apply IHaxms. beq_to_eq. congruence.
  Qed.

  Theorem make_correct: forall axms x y,
    eq axms x y <-> equiv (make_graph axms) x y = true.
  Proof.
    intros. split.
    - apply make_correct_left.
    - apply make_correct_right.
  Qed.
End DisjointSetListPair.
