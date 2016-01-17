Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.

(******************************************************************************)
(* Chapter 1.6.4: Slice Categories                                            *)
(******************************************************************************)

Definition MorphismInTo  `{C:Category}(X:C) := { Y:C & Y~~{C}~~>X }.
Definition MorphismOutOf `{C:Category}(X:C) := { Y:C & X~~{C}~~>Y }.

Definition TriangleAbove `{C:Category}{X:C}(M1 M2:MorphismInTo X) :=
   { f:(projT1 M1)~~{C}~~>(projT1 M2) & f >>> (projT2 M2) ~~ (projT2 M1) }.
Definition TriangleBelow `{C:Category}{X:C}(M1 M2:MorphismOutOf X) :=
   { f:(projT1 M1)~~{C}~~>(projT1 M2) & (projT2 M1) >>> f ~~ (projT2 M2) }.

Program Instance SliceOver `(C:Category)(X:C) : Category (MorphismInTo X) TriangleAbove :=
{ id   := fun y1        => existT _   (id (projT1 y1)) _
; eqv  := fun a b f g   => eqv    _ _ (projT1 f) (projT1 g)
; comp := fun _ _ _ f g => existT _   (projT1 f >>> projT1 g) _
}.
  Next Obligation.
    destruct f. destruct g. destruct H0.  destruct H1. simpl in *. setoid_rewrite <- e.  setoid_rewrite <- e0. apply associativity.
    Defined.
  Next Obligation.
    simpl; setoid_rewrite associativity. reflexivity.
    Defined.

Instance SliceOverInclusion `{C:Category}(X:C) : Functor (SliceOver C X) C (fun x => projT1 x) :=
  { fmor := fun a b f => projT1 f }.
  intros; simpl in H; auto.
  intros. destruct a; simpl; auto.
  intros. simpl. reflexivity.
  Defined.

Program Instance SliceUnder `(C:Category)(X:C) : Category (MorphismOutOf X) TriangleBelow :=
{ id   := fun y1        => existT _   (id (projT1 y1)) _
; eqv  := fun a b f g   => eqv    _ _ (projT1 f) (projT1 g)
; comp := fun _ _ _ f g => existT _   (projT1 f >>> projT1 g) _
}.
  Next Obligation.
    destruct f. destruct g. destruct H0.  destruct H1. simpl in *. setoid_rewrite <- associativity.
    setoid_rewrite e. auto.
    Defined.
  Next Obligation.
    simpl; setoid_rewrite associativity. reflexivity.
    Defined.

Instance SliceUnderInclusion `{C:Category}(X:C) : Functor (SliceUnder C X) C (fun x => projT1 x) :=
  { fmor := fun a b f => projT1 f }.
  intros; simpl in H; auto.
  intros. destruct a; simpl; auto.
  intros. simpl. reflexivity.
  Defined.
