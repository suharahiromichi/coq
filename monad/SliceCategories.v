Generalizable All Variables.
Require Import Notations.
Require Import Categories.
Require Import Functors.
Require Import Isomorphisms.

(******************************************************************************)
(* Chapter 1.6.4: Slice Categories                                            *)
(******************************************************************************)

Locate "{ _ : _ & _ }".                     (* "{ x : A  & P }" := sigT (fun x : A => P) *)
Definition MorphismInTo  `{C : Category} (X : C) := { Y : C & Y ~~{C}~~> X }.
Definition MorphismOutOf `{C : Category} (X : C) := { Y : C & X ~~{C}~~> Y }.
Check @MorphismInTo : ∀ (Obj : Type) (Hom : Obj → Obj → Setoid) (C : Category Hom),
    C → Type.
Check MorphismInTo _ : Type.                (* 引数は対象 *)

Definition TriangleAbove `{C : Category} {X : C} (M1 M2 : MorphismInTo X) :=
   {f : (projT1 M1) ~~{C}~~> (projT1 M2) & (projT2 M2) \\o f === (projT2 M1)}.
Definition TriangleBelow `{C : Category} {X : C} (M1 M2 : MorphismOutOf X) :=
   {f : (projT1 M1) ~~{C}~~> (projT1 M2) & f \\o (projT2 M1) === (projT2 M2)}.
(* 
(projT1 M1) ~~{C}~~> (projT1 M2) は Setoid
(projT2 M2) \\o f === (projT2 M1) は Prop
 *)
Check TriangleAbove _ _ : Type.
(*
TriangleAbove M1 M1 は、
(projT1 M1) ~~{C}~~> (projT1 M2) のサブタイプ (サブSetoid）で、
それを f とたときに、
(projT2 M2) \\o f === (projT2 M1) を満たすもの。
 *)

Instance SliceTAbove : forall `{C : Category} {X : C} (M1 M2 : MorphismInTo X), Setoid :=
  {|
    carrier := TriangleAbove M1 M2
  |}.

Check projT1.
Check @id.
Program Instance SliceOver `(C : Category) (X : C) : @Category (MorphismInTo X) SliceTAbove :=
  {|
    id   := fun y1        => existT _ (@id _ _ _ _ (projT1 _ y1)) _
  |}.
                                   


Obligation 1.                               (* projT2 a \\o id === projT2 a *)
Proof.
  rewrite /TriangleAbove.
  apply: (existT _ id).
  rewrite right_identity.
  reflexivity.
Defined.
Obligation 2.
Proof.
  rewrite /TriangleAbove.
  Check fun f g => existT _ (projT1 g \\o projT1 f) _.
  apply: (fun _ _ f g => existT _ (projT1 g \\o projT1 f)).
  - apply Obj.
  - move=> T. apply Obj.
  - move=> H H2. apply X.
  - move=> H H0 H1. apply Obj.
  - move=> H H0 H1 H2. apply Obj.
  - apply X.
  - simpl. apply X.
  - case X0; case X1.
    move=> F1 H1 F2 H2.
    admit.
  - admit.
  - admit.
Defined.
Obligation 3.
Proof.
  rewrite /SliceOver_obligation_1 /SliceOver_obligation_2.
  admit.
Defined.
Obligation 4.

{ 
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
    setoid_rewrit: ∀ (Obj : Type) (Hom : Obj → Obj → Setoid) (C : Category Hom),
       C → Type: ∀ (Obj : Type) (Hom : Obj → Obj → Setoid) (C : Category Hom),
       C → Type_e e. auto.
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
