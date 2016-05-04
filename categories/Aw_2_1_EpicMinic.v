Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.

(******************************************************************************)
(* Chapter 2.1: Epic and Monic morphisms                                      *)
(******************************************************************************)

(* Definition 2.1a *)
Class Monic `{C:Category}{a b:C}(f:a~>b) : Prop := 
  monic : forall c (g1 g2:c~>a), g1>>>f ~~ g2>>>f -> g1~~g2.
Implicit Arguments monic [ C a b Ob Hom ].

(* Definition 2.1b *)
Class Epic `{C:Category}{a b:C}(f:a~>b) : Prop := 
  epic : forall c (g1 g2:b~>c), f>>>g1 ~~ f>>>g2 -> g1~~g2.
Implicit Arguments epic [ C a b Ob Hom ].

(* Proposition 2.6 *)
Instance iso_epic `(i:Isomorphic) : Epic #i.
  simpl; unfold Epic; intros.
  setoid_rewrite <- left_identity.
  setoid_rewrite <- iso_comp2.
  setoid_rewrite associativity.
  setoid_rewrite H; reflexivity.
  Qed.

(* Proposition 2.6 *)
Instance iso_monic `(i:Isomorphic) : Monic #i.
  simpl; unfold Monic; intros.
  setoid_rewrite <- right_identity.
  setoid_rewrite <- iso_comp1.
  setoid_rewrite <- associativity.
  setoid_rewrite H; reflexivity.
  Qed.

(* a BiMorphism is an epic monic *)
Class BiMorphism `{C:Category}{a b:C}(f:a~>b) : Prop :=
{ bimorphism_epic  :> Epic  f
; bimorphism_monic :> Monic f
}.
Coercion bimorphism_epic  : BiMorphism >-> Epic.
Coercion bimorphism_monic : BiMorphism >-> Monic.

Class EndoMorphism `{C:Category}(A:C) :=
  endo : A ~> A.

Class AutoMorphism `{C:Category}(A:C) : Type :=
{ auto_endo1 : EndoMorphism A
; auto_endo2 : EndoMorphism A
; auto_iso   : Isomorphism  (@endo _ _ _ _ auto_endo1) (@endo _ _ _ _ auto_endo2)
}.

(*Class Balanced `{C:Category} : Prop :=
  balanced : forall (a b:C)(f:a~>b), BiMorphism f -> Isomorphism f.*)

