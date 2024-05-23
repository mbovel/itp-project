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

  Lemma ensure_repr_mono_none: forall ds x y,
    get ds x = None -> x <> y -> get (ensure_repr ds y) x = None.
  Proof.
    intros.
    unfold ensure_repr.
    destruct (get ds y) eqn:Heq.
    - assumption.
    - simpl.
      destruct (x =? y) eqn:Heqxy.
      + apply beq_correct in Heqxy. subst. rewrite H in Heq. contradiction.
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

  Lemma get_repr: forall ds x rx,
    get ds x = Some rx -> repr ds x = rx.
  Proof.
    intros.
    unfold repr.
    rewrite H. reflexivity.
  Qed.
  
  Definition union (ds: D) (x y: A) : D :=
    let xr := (repr ds x) in
    let yr := (repr ds y) in
    let ds' := (ensure_repr (ensure_repr ds xr) yr) in
    (replace_values ds' yr xr).


  Lemma beq_correct_false: forall x y,
    x =? y = false <-> x <> y.
  Proof.
    intros. split; intros.
    - intros H1. apply beq_correct in H1. rewrite H1 in H. discriminate.
    - destruct (x =? y) eqn:Heq.
      + apply beq_correct in Heq. contradiction.
      + reflexivity.
  Qed.

  Ltac name_term term name :=
    pose term as name;
    change term with name.

  Lemma union_different_same_repr: forall ds x y z,
    repr ds z <> repr ds y -> repr (union ds x y) z = repr ds z.
  Proof.
    intros.
    unfold union.
    name_term (ensure_repr (ensure_repr ds (repr ds x)) (repr ds y)) ds'.
    assert (repr ds' z = repr ds z). { eauto using ensure_repr_preserve. }
    assert (repr ds' y = repr ds y). { eauto using ensure_repr_preserve. }
    unfold repr at 1.
    destruct (get ds' z) as [rz|] eqn:Hgetz.
    - assert (repr ds z = rz). { apply get_repr in Hgetz. congruence. }
      rewrite replace_values_correct_neq with (v := rz); congruence.
    - assert (repr ds z = z). { rewrite <- H0. unfold repr. rewrite Hgetz. reflexivity. }
      rewrite replace_values_correct_neq_none; congruence.
  Qed.

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

  Theorem union_correct: forall ds x x' y y',
    (equiv ds x x' = true) ->
    (equiv ds y y' = true) ->
    (equiv (union ds x y) x' y' = true).
  Proof.
    intros.
    unfold union.
    unfold equiv in H, H0.
    rewrite beq_correct in *.
    name_term (ensure_repr (ensure_repr ds (repr ds x)) (repr ds y)) ds'.
    assert (get ds' x' = Some (repr ds x)). { eauto using ensure_repr_get_2, ensure_repr_mono. }
    assert (get ds' y' = Some (repr ds y)). { eauto using ensure_repr_get_2, ensure_repr_preserve. }
    apply union_correct_1; assumption.
  Qed.

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
    apply beq_correct in Heq.
    assert (equiv ds x y = true); try unfold equiv; try rewrite beq_correct; try congruence.
    assert (equiv ds x z = true); try unfold equiv; try rewrite beq_correct; try congruence.
    assert (equiv ds y z = true); try unfold equiv; try rewrite beq_correct; try congruence.
    assert (equiv ds z y = true); try unfold equiv; try rewrite beq_correct; try congruence.

  
    assert (equiv ds z z = true); try unfold equiv; try rewrite beq_correct; try congruence.
    assert (equiv ds w w = true); try unfold equiv; try rewrite beq_correct; try congruence.
    assert (equiv ds z x = true); try unfold equiv; try rewrite beq_correct; try congruence.

    pose proof (union_correct ds w w z x). 
    rewrite H5 in H7. rewrite H6 in H7.
    specialize (H7 (reflexivity _) (reflexivity _)).
    pose proof (union_correct ds w w z y). 
    rewrite H5 in H8. rewrite H3 in H8.
    specialize (H8 (reflexivity _) (reflexivity _)).
    unfold equiv in H7, H8. rewrite beq_correct in H7, H8. congruence.

    (* Uneeded case analysis on xr =? wr, kept as reference *)
    (* destruct (xr =? wr) eqn:Heqxrwr.
    - apply beq_correct in Heqxrwr.
      assert (equiv ds w x = true); try unfold equiv; try rewrite beq_correct; try congruence.
      pose proof (union_correct ds  w x z y).
      rewrite H4 in H5. rewrite H3 in H5. 
      specialize (H5 (reflexivity _) (reflexivity _)).
      unfold equiv in H5. rewrite beq_correct in H5. congruence.
    - rewrite beq_correct_false in Heqxrwr. 
      assert (equiv ds x w = false); try unfold equiv; try rewrite beq_correct_false; try congruence.
      assert (equiv ds w x = false); try unfold equiv; try rewrite beq_correct_false; try congruence.
      assert (equiv ds z z = true); try unfold equiv; try rewrite beq_correct; try congruence.
      assert (equiv ds w w = true); try unfold equiv; try rewrite beq_correct; try congruence.
      assert (equiv ds z x = true); try unfold equiv; try rewrite beq_correct; try congruence.
      pose proof (union_correct ds w w z x). 
      rewrite H7 in H9. rewrite H8 in H9.
      specialize (H9 (reflexivity _) (reflexivity _)).
      pose proof (union_correct ds w w z y). 
      rewrite H7 in H10. rewrite H3 in H10.
      specialize (H10 (reflexivity _) (reflexivity _)).
      unfold equiv in H9, H10. rewrite beq_correct in H9, H10. congruence. *)

    + (* In this case, the representant of x and y will not change *)
      apply beq_correct_false in Heq.
      rewrite (union_different_same_repr ds w z x); try congruence.
      ++ rewrite (union_different_same_repr ds w z y); congruence.

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
          (* Will need to prove that union(a,b) is equivalent to union(b,a) -> Nope haha *)
  Qed.

  Lemma union_repr_2: forall ds x z w,
    repr ds x = repr ds z ->
    repr (union ds z w) x = repr ds z.
  Proof.
    intros.
    unfold union.
    name_term (ensure_repr (ensure_repr ds (repr ds z)) (repr ds w)) ds'.
    assert (get ds' x = Some (repr ds z)). { eauto using ensure_repr_get_2, ensure_repr_mono. }
    unfold repr at 1.
    destruct (eq_dec (repr ds w) (repr ds z)).
    - rewrite e, (replace_values_correct ds' x (repr ds z) (repr ds z)); auto.
    - rewrite replace_values_correct_neq with (v := repr ds z); auto.
  Qed.

  Lemma union_repr_3: forall ds x w z,
    repr ds x = repr ds w ->
    repr (union ds z w) x = repr ds z.
  Proof.
    intros.
    unfold union.
    name_term (ensure_repr (ensure_repr ds (repr ds z)) (repr ds w)) ds'.
    assert (get ds' x = Some (repr ds w)). { eauto using ensure_repr_get_2, ensure_repr_preserve. }
    unfold repr at 1.
    rewrite (replace_values_correct ds' x (repr ds w) (repr ds z)); auto.
  Qed.
      
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
      apply eq_nonempty.
      destruct (equiv (make_graph axms) x y) eqn:Hxy.
      + left. apply IHaxms. assumption.
      + right.
        remember (make_graph axms) as ds.
        assert (forall x y : A, repr ds x = repr ds y -> eq axms x y) as IHaxms'.
        {
          intros.
          apply IHaxms.
          unfold equiv.
          rewrite beq_correct.
          assumption.
        }
        destruct (equiv ds x w) eqn:Hxw, (equiv ds y w) eqn:Hyw;
            unfold equiv in *;
            rewrite nbeq_correct, beq_correct in *.
        * pose proof (union_repr_2 ds x w z Hxw) as H1.
          pose proof (union_repr_2 ds y w z Hyw) as H2.
          congruence.
        * pose proof (union_repr_3 ds x w z Hxw) as H1.
          pose proof (union_different_same_repr ds z w y Hyw) as H2.
          right. split; apply IHaxms'; congruence.
        * pose proof (union_repr_3 ds y w z Hyw) as H1.
          pose proof (union_different_same_repr ds z w x Hxw) as H2.
          left. split; apply IHaxms'; congruence.
        * pose proof (union_different_same_repr ds z w x Hxw) as H1.
          pose proof (union_different_same_repr ds z w y Hyw) as H2.
          congruence.    
  Qed.

  Theorem make_correct: forall axms x y,
    eq axms x y <-> equiv (make_graph axms) x y = true.
  Proof.
    intros. split.
    - apply make_correct_left.
    - apply make_correct_right.
  Qed.
End DisjointSetListPair.
