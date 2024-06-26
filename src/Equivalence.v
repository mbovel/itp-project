Require Import Coq.Lists.List.
Import ListNotations.
Require Import String.

Inductive eq {A} (axms : list (A * A)) : A -> A -> Prop :=
  | eq_axms: forall x y: A, In (x, y) axms -> eq axms x y
  | eq_refl: forall x: A, eq axms x x
  | eq_sym: forall x y: A, eq axms y x -> eq axms x y
  | eq_trans: forall x y z: A, eq axms x y -> eq axms y z -> eq axms x z.

Module StringEqExample.
   Open Scope string_scope.
   Import List.
   Import ListNotations.

   Definition l := [("a", "b"); ("b", "c"); ("d", "e")].

   Lemma test: (eq l "a" "b").
   Proof.
      eapply eq_axms. simpl. left. reflexivity.
   Qed.

   Lemma test2: (eq l "a" "c").
   Proof.
      eapply eq_trans.
      - eapply eq_axms. simpl. left. reflexivity.
      - eapply eq_axms. simpl. right. left. reflexivity.
   Qed.
End StringEqExample.

Lemma eq_empty: forall {A} (x y: A), (eq [] x y) <-> x = y.
Proof.
  intros. split.
  - intros. induction H; try contradiction; subst; reflexivity.
  - intros. subst. apply eq_refl.
Qed.

Lemma eq_mono: forall {A} (x y w z: A) (axms: list (A * A)) (a: A),
   (eq axms x y)
   -> (eq ((w, z) :: axms) x y).
Proof.
   intros.
   induction H.
   - apply eq_axms. simpl. right. assumption.
   - apply eq_refl.
   - apply eq_sym. assumption.
   - pose proof (eq_trans ((w, z) :: axms) x y z0 IHeq1 IHeq2).
     assumption.
Qed.

Lemma eq_join: forall {A} (x x' y y': A) (axms: list (A * A)) (a: A),
   (eq axms x x') ->
   (eq axms y y') ->
   (eq ((x', y') :: axms) x y).
Proof.
   intros.
   apply eq_trans with (y := x').
   - apply eq_mono; assumption.
   - apply eq_trans with (y := y').
     + apply eq_axms. unfold In. left. reflexivity.
     + apply eq_sym. apply eq_mono; assumption.
Qed.

Lemma eq_nonempty: forall {A} (x y z w: A) (axms: list (A * A)),
   (
     (eq axms x y)
     \/ (eq axms x z /\ eq axms y w)
     \/ (eq axms x w /\ eq axms y z)
   )
   -> eq ((z, w) :: axms) x y.
Proof.
   intros.
   destruct H.
   - apply eq_mono; assumption.
   - destruct H.
     + destruct H. auto using eq_join, eq_sym.
     + apply eq_sym. destruct H. auto using eq_join, eq_sym.
Qed.

Lemma eq_nonempty_inverse: forall {A} (x y z w: A) (axms: list (A * A)),
   eq ((z, w) :: axms) x y
   -> (
     (eq axms x y)
     \/ (eq axms z x /\ eq axms w y)
     \/ (eq axms w x /\ eq axms z y)
   ).
Proof.
   intros.
   induction H.
   - destruct H.
     + injection H. intros. subst. clear H.
       right. left. split; apply eq_refl.
     + left. apply eq_axms. simpl. assumption.
   - left. apply eq_refl.
   - destruct IHeq.
     + left. apply eq_sym. assumption.
     + destruct H0; right; [right | left]; destruct H0; split; assumption.
   - destruct IHeq1, IHeq2.
       + eauto using eq_trans, eq_sym.
       + destruct H2; destruct H2; right; [left | right]; eauto using eq_trans, eq_sym.
       + destruct H1; destruct H1; eauto using eq_trans, eq_sym.
       + destruct H1, H2; destruct H1, H2; eauto using eq_trans, eq_sym.    
Qed.
