Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.Equalities.
Import List.
Import ListNotations.

Class BoolEq A := {
  beq : A -> A -> bool;
  beq_correct : forall x y : A, beq x y = true <-> x = y
}.

Notation "x =? y" := (beq x y) (at level 70).

(*
Instance string_BoolEq : BoolEq string := {
  beq := String.eqb;
  beq_correct := String.eqb_eq
}.
*)

Class DisjointSet D {A} {ev: BoolEq A} := {  
  empty : D;
  union : D -> A -> A -> D;
  equiv : D -> A -> A -> bool;
}.

Record list_disjoint_set A := {
  elems: list (list A)
}.

Definition contains {A: Type} {ev: BoolEq A} (l: list A) (x: A)  : bool :=
  match (List.find (fun y => y =? x) l) with
  | Some _ => true
  | None => false
  end.

Instance list_disjoint_set_DisjointSet A {ev: BoolEq A} : DisjointSet (list_disjoint_set A) := {
  empty := {| elems := [] |};
  union (ds: list_disjoint_set A) x y := 
    let (elems) := ds in
    let lx := List.find (fun l => contains l x) elems in
    let ly := List.find (fun l => contains l y) elems in
    match lx, ly with
    | Some lx, Some ly => 
      let elems' := List.filter (fun l => (negb (l =? lx)) && (negb (l =? ly))) elems in
      {| elems := (lx ++ ly) :: elems' |}
    | Some lx, None => {| elems := lx :: elems |}
    | None, Some ly => {| elems := ly :: elems |}
    | None, None => {| elems := [x; y] :: elems |}
    end;
  equiv (ds: list_disjoint_set A) x y :=
    let (elems) := ds in
    match (List.find (fun l => contains l x) elems), (List.find (fun l => contains l y) elems) with
    | Some lx, Some ly => lx =? ly
    | _, _ => false
    end;
}.

Check (empty list_disjoint_set string).

Compute (empty).
