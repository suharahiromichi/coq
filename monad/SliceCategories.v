Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import finset fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.
Require Import Notations.
Require Import Categories.
Require Import Functors.
Require Import Isomorphisms.

(******************************************************************************)
(* Chapter 1.6.4: Slice Categories                                            *)
(******************************************************************************)
Locate "{ _ : _ & _ }".                     (* "{ x : A  & P }" := sigT (fun x : A => P) *)
(* X が 圏Cの対象であるとき、 *)
(* cod(f) = X である圏Cの射fの集まり *)
Definition MorphismInTo  `{C : Category} (X : C) := {Y : C & Y ~~{C}~~> X}.
(* dom(f) = X である圏Cの射fの集まり *)
Definition MorphismOutOf `{C : Category} (X : C) := {Y : C & X ~~{C}~~> Y}.
Check @MorphismInTo : ∀ (Obj : Type) (Hom : Obj → Obj → Setoid) (C : Category Hom),
    C → Type.
Check MorphismInTo _ : Type.                (* 引数は対象 *)

Check projT1 : ∀ (A : Type) (P : A → Type), sigT P → A.
Check projT2 : ∀ (A : Type) (P : A → Type) (x : sigT P), P (projT1 x).

Section SliceExample.
  Check Sets.                               (* 圏Sets *)
  Variable X : Sets.                        (* 圏Setsの対象 *)
  Variable M : MorphismInTo X.              (* 圏Setsの対象Xをcodとする射、cod(M)=X *)
  Check projT1 M : Sets.                    (* 圏Setsの対象 *)
  Check projT2 M : (λ Y : Sets, Y ~~{ Sets }~~> X) (projT1 M).
  Check projT2 M : (fun (Y : Sets) => (Y ~~{ Sets }~~> X)) (projT1 M).
  Check projT2 M : ((projT1 M) ~~{ Sets }~~> X).
  Check projT2 M : ((projT1 M) ~> X).       (* cod(f)=Xなる射 *)
  
  Check @id (projT1 M).
End SliceExample.

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
TriangleAbove M1 M2 は、
(projT1 M1) ~~{C}~~> (projT1 M2) のサブタイプ で、
それを f しとたときに、
(projT2 M2) \\o f === (projT2 M1) を満たすもの。

すなわち、次の可換図を満たす f :

                f
   projT1(M1) -----> projT1(M2)
            \       /
             \     /        
       M1     \   /     M2
               V V
                X
*)

Check @eqv.

Program Instance EquivSlice : forall `{C : Category} {X : C} (M1 M2 : MorphismInTo X),
    Equivalence (@eq C).
Print EquivSlice.
(* 
Equivalence_Reflexive := eq_Reflexive;
Equivalence_Symmetric := eq_Symmetric;
Equivalence_Transitive := eq_Transitive |}
     : ∀Obj Hom C X _ _, Equivalence eq
 *)

Check eqv_equivalence.
Check EquivSlice.

Program Instance SliceTAbove' : forall `{C : Category} {X : C} (M1 M2 : MorphismInTo X), Setoid :=
  {|
    carrier := TriangleAbove M1 M2;
    eqv := fun f g => (projT1 f = projT1 g)
  |}.
Obligation 1.
Proof.
  split.
  - by case.
  - by case.
  - move=> f g h /= Hfg Hgh.
      by rewrite Hfg Hgh.
Defined.

Program Instance SliceTAbove : forall `{C : Category} {X : C} (M1 M2 : MorphismInTo X), Setoid :=
  {|
    carrier := TriangleAbove M1 M2;
    eqv := fun f g => (projT1 f === projT1 g)
  |}.
Obligation 1.
Proof.
  split.
  - case=> f Hf.
    reflexivity.
  - move=> f g /= Hfg.
    rewrite Hfg.
    reflexivity.
  - move=> f g h /= Hfg Hgh.
    rewrite Hfg Hgh.
    reflexivity.
Defined.

Check @comp : ∀Obj Hom Category a b c _ _, a ~~{ Category }~~> c.
Check comp _ _ : _ ~~{ _ }~~> _.

Program Instance SliceOver `(C : Category) (X : C) : @Category (MorphismInTo X) SliceTAbove :=
  {|
    id  := fun y1 => existT _ (@id _ _ (projT1 y1)) _;
    comp := fun _ _ _ f g => existT _ ((projT1 f) \\o (projT1 g)) _
  |}.
Obligation 1.                               (* projT1 y1 ~~{ C }~~> projT1 y1 *)
Proof.
  by apply id.
Defined.
Obligation 2.                               (* projT2 y1 \\o id === projT2 y1 *)
Proof.
  rewrite /SliceOver_obligation_1.
  rewrite right_identity.
  reflexivity.
Defined.
Obligation 3.                               (* projT2 c \\o (projT1 f \\o projT1 g) === projT2 a *)
Proof.
  move: H H0 H1 f g => a b c f g.
  case: f => MORbc Hcbc_b.
  case: g => MORab Hbab_a.
  simpl.
  rewrite -associativity.
  rewrite Hcbc_b Hbab_a.
  reflexivity.
Defined.
Obligation 4.
Proof.
  move=> fbc fbc' Hbc fab fab' Hab /=.
  rewrite Hbc Hab.
  reflexivity.
Defined.
Obligation 5.
Proof.
  rewrite /SliceOver_obligation_1.
  rewrite left_identity.
  reflexivity.
Defined.
Obligation 6.
  rewrite /SliceOver_obligation_1.
  rewrite right_identity.
  reflexivity.
Defined.

(* ここまで *)

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
