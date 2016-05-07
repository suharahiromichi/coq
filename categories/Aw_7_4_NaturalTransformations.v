From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Generalizable All Variables. *)
Require Import Aw_0_Notations.
Require Import Aw_1_3_Categories.
Require Import Aw_1_4_Functors.
Require Import Aw_1_5_Isomorphisms.

(*******************************************************************************)
(* Chapter 7.4: Natural Transformations                                        *)
(*******************************************************************************)

(* Definition 7.6 *)

Generalizable Variable A B.
Class NaturalTransformation `{C1 : Category} `{C2 : Category} {Fobj1 Fobj2 : C1 -> C2}
      (F1 : @Functor C1 _ _ C2 _ _ Fobj1) (F2 : @Functor C1 _ _ C2 _ _ Fobj2) :=
  {
    nt_component : forall c : C1, (Fobj1 c) ~~{C2}~~> (Fobj2 c);
    nt_commutes  : forall `(f : A ~> B),
                     F2 \ f \\o (nt_component A) === (nt_component B) \\o F1 \ f
  }.
Notation "F ~~~> G" := (@NaturalTransformation _ _ _ _ _ _ _ _ F G) : category_scope.
Coercion nt_component : NaturalTransformation >-> Funclass.

(* the identity natural transformation *)
Program Instance nt_id `{C : Category} `{D : Category} {Fobj}
           (F : @Functor C _ _ D _ _ Fobj) : NaturalTransformation F F.
Obligation 1.
Proof.
  Check c.
  Check F c.
  Check @iid _ _ _ c.
  Check (fun c => @iid _ _ _ (F c)).  
  Check (@Build_NaturalTransformation _ _ _ _ _ _ _ _ F F (fun c => @iid _ _ _ (F c))).
  apply (@Build_NaturalTransformation _ _ _ _ _ _ _ _ F F (fun c => @iid _ _ _ (F c))).
  setoid_rewrite left_identity.
  setoid_rewrite right_identity.
  reflexivity.
Defined.
Obligation 2.
Proof.
  setoid_rewrite left_identity.
  setoid_rewrite right_identity.
  reflexivity.
Defined.  

Program Instance nt_comp `{C : Category}`{D : Category}
  {Fobj}{F : @Functor C _ _ D _ _ Fobj}
  {Gobj}{G : @Functor C _ _ D _ _ Gobj}
  {Hobj}{H : @Functor C _ _ D _ _ Hobj}
  (nt_f_g : F ~~~> G) (nt_g_h : G ~~~> H) : F ~~~> H.
Obligation 1.
Proof.
  Check (fun c => nt_g_h c \\o nt_f_g c) : (forall c : C, Fobj c ~~{ D }~~> Hobj c).
  apply (@Build_NaturalTransformation _ _ _ _ _ _ _ _ F H (fun c => nt_g_h c \\o nt_f_g c)).
  set (@nt_commutes _ _ C _ _ D _ _ F G nt_f_g) as comm1.
  set (@nt_commutes _ _ C _ _ D _ _ G H nt_g_h) as comm2.
  intros.
  setoid_rewrite associativity.
  setoid_rewrite <- comm1.
  setoid_rewrite <- associativity.
  setoid_rewrite comm2.
  reflexivity.
Defined.
Obligation 2.
  set (@nt_commutes _ _ C _ _ D _ _ F G nt_f_g) as comm1.
  set (@nt_commutes _ _ C _ _ D _ _ G H nt_g_h) as comm2.
  setoid_rewrite associativity.
  setoid_rewrite <- comm1.
  setoid_rewrite <- associativity.
  setoid_rewrite comm2.
  reflexivity.
Defined.

(* END *)
