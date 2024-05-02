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
      econstructor. simpl. left. reflexivity.
   Qed.

   Lemma test2: (eq l "a" "c").
   Proof.
      eapply eq_trans.
      - eapply eq_axms. simpl. left. reflexivity.
      - apply eq_axms. simpl. right. left. reflexivity.
   Qed.
End StringEqExample.

Lemma eq_empty: forall {A} (x y: A), (eq [] x y) <-> x = y.
Proof.
  intros. split.
  - intros. induction H; try contradiction; subst; reflexivity.
  - intros. subst. apply eq_refl.
Qed.

Lemma eq_nonempty': forall {A} (x y z: A) (axms: list (A * A)),
   ((eq axms x z) \/ (eq axms y z)) -> ((eq ((x, y) :: axms) x z) /\ (eq ((x, y) :: axms) y z)).
Proof.
Admitted.

Lemma eq_nonempty: forall {A} (x y z w: A) (axms: list (A * A)),
   ((eq axms x z) \/ (eq axms y z)) -> ((eq ((z, w) :: axms) x z) /\  (eq ((z, w) :: axms) y w)).
Proof.
Admitted.
