From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Generalizable All Variables. *)
Require Import Aw_0_Notations.
Require Import Aw_1_3_Categories.
Require Import Aw_1_4_Functors.
Require Import Aw_1_5_Isomorphisms.

(******************************************************************************)
(* Chapter 2.1: Epic and Monic morphisms                                      *)
(******************************************************************************)

(* Definition 2.1a *)
Class Monic `{C : Category} {a b : C} (f : a ~> b) : Prop :=
  monic : forall c (g1 g2 : c ~> a), f \\o g1 === f \\o g2 -> g1 === g2.
(* Implicit Arguments monic [ C a b Ob Hom ]. *)

(* Definition 2.1b *)
Class Epic `{C : Category} {a b : C} (f : a ~> b) : Prop := 
  epic : forall c (g1 g2 : b~>c), g1 \\o f === g2 \\o f -> g1 === g2.
(* Implicit Arguments epic [ C a b Ob Hom ]. *)

(* Proposition 2.6 *)
(* すべての同型は、エピepiである。 *)
Instance iso_epic `(i : Isomorphic) : Epic #i.
Proof.
  rewrite /Epic => c g1 g2 H.
  rewrite -[g1]right_identity -[g2]right_identity.
  rewrite -iso_comp2 -2!associativity.
  rewrite H.
  reflexivity.
Qed.

(* Proposition 2.6 *)
(* すべての同型は、モノmonicである。 *)
Instance iso_monic `(i : Isomorphic) : Monic #i.
Proof.
  rewrite /Monic => c g1 g2 H.
  rewrite -[g1]left_identity -[g2]left_identity.
  rewrite -iso_comp1 2!associativity.
  rewrite H.
  reflexivity.
Qed.

(* a BiMorphism is an epic monic *)
Class BiMorphism `{C : Category} {a b : C} (f : a ~> b) : Prop :=
  {
    bimorphism_epic  :> Epic  f;
    bimorphism_monic :> Monic f
  }.
Coercion bimorphism_epic  : BiMorphism >-> Epic.
Coercion bimorphism_monic : BiMorphism >-> Monic.

Class EndoMorphism `{C : Category} (A : C) :=
  endo : A ~> A.

Class AutoMorphism `{C : Category} (A : C) : Type :=
  {
    auto_endo1 : EndoMorphism A;
    auto_endo2 : EndoMorphism A;
    auto_iso   : Isomorphism  (@endo _ _ _ _ auto_endo1) (@endo _ _ _ _ auto_endo2);
  }.

(*Class Balanced `{C:Category} : Prop :=
  balanced : forall (a b:C)(f:a~>b), BiMorphism f -> Isomorphism f.*)

