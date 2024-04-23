Require Import Coq.Lists.List.
Import List.
Import ListNotations.

Require Import String.
Open Scope string_scope.

Inductive eq {A : Type} (axms : list (A * A)) : A -> A -> Prop :=
  | eq_axms: forall x y: A, In (x, y) axms -> eq axms x y
  | eq_refl: forall x: A, eq axms x x
  | eq_sym: forall x y: A, eq axms y x -> eq axms x y
  | eq_trans: forall x y z: A, eq axms x y -> eq axms y z -> eq axms x z.


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