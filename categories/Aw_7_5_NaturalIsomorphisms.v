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
(* Chapter 7.5: Natural Isomorphisms                                           *)
(*******************************************************************************)

Generalizable Variable A B.

(* Definition 7.10 *)
Class NaturalIsomorphism `{C1 : Category} `{C2 : Category} {Fobj1 Fobj2 : C1 -> C2}
      (F1 : @Functor C1 _ _ C2 _ _ Fobj1) (F2 : @Functor C1 _ _ C2 _ _ Fobj2) :=
  {
    ni_iso      : forall A, Fobj1 A ≅ Fobj2 A;
    ni_commutes : forall `(f : A ~> B),
                    F2 \ f \\o #(ni_iso A) === #(ni_iso B) \\o F1 \ f 
  }.
Arguments ni_iso {Obj Hom Obj0 Hom0 C1 C2 Fobj1 Fobj2 F1 F2} Ni A : rename.
Arguments ni_commutes {Obj Hom Obj0 Hom0 C1 C2 Fobj1 Fobj2 F1 F2} Ni A B f : rename.
Check ni_commutes.

(* FIXME: coerce to NaturalTransformation instead *)

Coercion ni_iso : NaturalIsomorphism >-> Funclass.
Notation "F <~~~> G" := (@NaturalIsomorphism _ _ _ _ _ _ _ _ F G) : category_scope.

(* same as ni_commutes, but phrased in terms of inverses *)
Lemma ni_commutes' `(ni : NaturalIsomorphism) :
  forall `(f : A ~> B),
    #(ni_iso ni B)⁻¹ \\o F2 \ f === F1 \ f \\o #(ni_iso ni A)⁻¹.
Proof.
  intros.
  apply iso_shift_right'.
  setoid_rewrite associativity.
  symmetry.
  apply iso_shift_left'.
  symmetry.
  apply ni_commutes.
Qed.

(* FIXME: Lemma 7.11: natural isos are natural transformations in which every morphism is an iso *)

(* every natural iso is invertible, and that inverse is also a natural iso *)

Generalizable Variable Fa Fb.

Definition ni_inv `(N : NaturalIsomorphism (F1 := Fa) (F2 := Fb)) : NaturalIsomorphism Fb Fa.
Proof.
  Check @Build_NaturalIsomorphism.
  Check @Build_NaturalIsomorphism _ _ _ _ _ _ _ _ Fb Fa.
  Check (fun A : C1 => @iso_inv _ _ _ _ _ (ni_iso N A)). (* ∀ A : C1, Fobj2 A ≅ Fobj1 A *)
  Check (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _ Fb Fa (fun A : C1 => @iso_inv _ _ _ _ _ (ni_iso N A))).

  apply (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _ Fb Fa (fun A : C1 => @iso_inv _ _ _ _ _ (ni_iso N A))).
  move=> A' B f /=.
  Check ni_commutes N A' B f.
  have qqq := ni_commutes N A' B f.
  symmetry in qqq.
  apply iso_shift_left' in qqq.  
  rewrite qqq.
  rewrite 2!associativity.
  rewrite [# (N A') \\o iso_backward (N A')]iso_comp2.
  rewrite right_identity.
  reflexivity.
Defined.
  
Definition ni_id `{C1 : Category} `{C2 : Category} {Fobj}
           (F : @Functor C1 _ _ C2 _ _ Fobj) : NaturalIsomorphism F F.
Proof.
  Check @Build_NaturalIsomorphism _ _ _ _ _ _ _ _ F F.
  Check (fun A : C1 => @iso_id _ _ _ (F A)).
  Check @Build_NaturalIsomorphism _ _ _ _ _ _ _ _ F F (fun A : C1 => @iso_id _ _ _ (F A)).

  apply (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _ F F (fun A : C1 => @iso_id _ _ _ (F A))).
  move=> A B f /=.
  rewrite left_identity.
  rewrite right_identity.
  reflexivity.
Defined.

(* two different choices of composition order are naturally isomorphic (strictly, in fact) *)
Program Instance ni_associativity `{C1 : Category} `{C2 : Category} `{C3 : Category} `{C4 : Category}
  {Fobj1} (F1 : @Functor C1 _ _ C2 _ _ Fobj1)
  {Fobj2} (F2 : @Functor C2 _ _ C3 _ _ Fobj2)
  {Fobj3} (F3 : @Functor C3 _ _ C4 _ _ Fobj3) : ((F1 >>>> F2) >>>> F3) <~~~> (F1 >>>> (F2 >>>> F3)).
Obligation 1.
Proof.
  Check @iso_id.
  Check @iso_id _ _ _ (F3 (F2 (F1 A))).
  by apply (@iso_id _ _ _ (F3 (F2 (F1 A)))).
Defined.
Obligation 2.
Proof.
  rewrite left_identity.
  rewrite right_identity.
  reflexivity.
Defined.

(*
Definition ni_comp `{C:Category}`{D:Category}
   {F1Obj}{F1:@Functor _ _ C _ _ D F1Obj}
   {F2Obj}{F2:@Functor _ _ C _ _ D F2Obj}
   {F3Obj}{F3:@Functor _ _ C _ _ D F3Obj}
   (N1:NaturalIsomorphism F1 F2)
   (N2:NaturalIsomorphism F2 F3)
   : NaturalIsomorphism F1 F3.
   intros.
     destruct N1 as [ ni_iso1 ni_commutes1 ].
     destruct N2 as [ ni_iso2 ni_commutes2 ].
   exists (fun A => iso_comp (ni_iso1 A) (ni_iso2 A)).
   abstract (intros; simpl;
             setoid_rewrite <- associativity;
             setoid_rewrite <- ni_commutes1;
             setoid_rewrite associativity;
             setoid_rewrite <- ni_commutes2;
             reflexivity).
   Defined.
*)

Definition ni_respects1 `{A : Category} `{B : Category}
           {Fobj} (F : @Functor A _ _ B _ _ Fobj)
           `{C : Category}
           {G0obj} (G0 : @Functor B _ _ C _ _ G0obj)
           {G1obj} (G1 : @Functor B _ _ C _ _ G1obj) :
  (G0 <~~~> G1) -> ((F >>>> G0) <~~~> (F >>>> G1)).
Proof.
  move=> phi.
  destruct phi as [ phi_niso phi_comm ].
  refine {| ni_iso := (fun a => phi_niso (Fobj a)) |}.
  intros; simpl; apply phi_comm.
Defined.

Definition ni_respects2
  `{A:Category}`{B:Category}
  {F0obj}(F0:Functor A B F0obj)
  {F1obj}(F1:Functor A B F1obj)
  `{C:Category}
  {Gobj}(G:Functor B C Gobj)
  : (F0 <~~~> F1) -> ((F0 >>>> G) <~~~> (F1 >>>> G)).
  intro phi.
  destruct phi as [ phi_niso phi_comm ].
  refine {| ni_iso := fun a => (@functors_preserve_isos _ _ _ _ _ _ _ G) _ _ (phi_niso a) |}.
  intros; simpl.
  setoid_rewrite fmor_preserves_comp.
  apply fmor_respects.
  apply phi_comm.
  Defined.

Definition ni_respects
  `{A : Category} `{B : Category}
  {F0obj}(F0 : Functor A B F0obj)
  {F1obj}(F1 : Functor A B F1obj)
  `{C : Category}
  {G0obj}(G0 : Functor B C G0obj)
  {G1obj}(G1 : Functor B C G1obj)
  : (F0 <~~~> F1) -> (G0 <~~~> G1) -> ((F0 >>>> G0) <~~~> (F1 >>>> G1)).
  intro phi.
  intro psi.
  destruct psi as [ psi_niso psi_comm ].
  destruct phi as [ phi_niso phi_comm ].
  refine {| ni_iso :=
      (fun a => iso_comp ((@functors_preserve_isos _ _ _ _ _ _ _ G0) _ _ (phi_niso a)) (psi_niso (F1obj a))) |}.
  abstract (intros; simpl;
            setoid_rewrite <- associativity;
            setoid_rewrite fmor_preserves_comp;
            setoid_rewrite <- phi_comm;
            setoid_rewrite <- fmor_preserves_comp;
            setoid_rewrite associativity;
            apply comp_respects; try reflexivity;
            apply psi_comm).
  Defined.

(*
 * Some structures (like monoidal and premonoidal functors) use the isomorphism
 * component of a natural isomorphism in an "informative" way; these structures
 * should use NaturalIsomorphism.
 *
 * However, in other situations the actual iso used is irrelevant; all
 * that matters is the fact that a natural family of them exists.  In
 * these cases we can speed up Coq (and the extracted program)
 * considerably by making the family of isos belong to [Prop] rather
 * than [Type].  IsomorphicFunctors does this -- it's essentially a
 * copy of NaturalIsomorphism which lives in [Prop].
 *)

(* Definition 7.10 *)
Definition IsomorphicFunctors `{C1 : Category} `{C2 : Category} {Fobj1 Fobj2 : C1->C2}(F1 : Functor C1 C2 Fobj1)(F2 : Functor C1 C2 Fobj2) :=
  exists  ni_iso      : (forall A, Fobj1 A ≅ Fobj2 A),
                         forall `(f : A~>B), #(ni_iso A) >>> F2 \ f ~~ F1 \ f >>> #(ni_iso B).
Notation "F ≃ G" := (@IsomorphicFunctors _ _ _ _ _ _ _ _ F G) : category_scope.

Definition if_id `{C : Category} `{D : Category} {Fobj}(F : Functor C D Fobj) : IsomorphicFunctors F F.
  exists (fun A => iso_id (F A)).
  abstract (intros;
            simpl;
            etransitivity;
            [ apply left_identity |
            symmetry;
            apply right_identity]).
  Qed.

(* every natural iso is invertible, and that inverse is also a natural iso *)
Definition if_inv
  `{C1 : Category} `{C2 : Category} {Fobj1 Fobj2 : C1->C2} {F1 : Functor C1 C2 Fobj1} {F2 : Functor C1 C2 Fobj2}
   (N : IsomorphicFunctors F1 F2)  :  IsomorphicFunctors F2 F1.
  intros.
    destruct N as [ ni_iso ni_commutes ].
    exists (fun A => iso_inv _ _ (ni_iso A)).
  intros; simpl.
    symmetry.
    set (ni_commutes _ _ f) as qq.
    symmetry in qq.
    apply iso_shift_left' in qq.
    setoid_rewrite qq.
    repeat setoid_rewrite <- associativity.
    setoid_rewrite iso_comp2.
    setoid_rewrite left_identity.
    reflexivity.
  Qed.

Definition if_comp `{C : Category} `{D : Category}
   {F1Obj} {F1 : @Functor _ _ C _ _ D F1Obj}
   {F2Obj} {F2 : @Functor _ _ C _ _ D F2Obj}
   {F3Obj} {F3 : @Functor _ _ C _ _ D F3Obj}
   (N1 : IsomorphicFunctors F1 F2)
   (N2 : IsomorphicFunctors F2 F3)
    :  IsomorphicFunctors F1 F3.
   intros.
     destruct N1 as [ ni_iso1 ni_commutes1 ].
     destruct N2 as [ ni_iso2 ni_commutes2 ].
   exists (fun A => iso_comp (ni_iso1 A) (ni_iso2 A)).
   abstract (intros; simpl;
             setoid_rewrite <- associativity;
             setoid_rewrite <- ni_commutes1;
             setoid_rewrite associativity;
             setoid_rewrite <- ni_commutes2;
             reflexivity).
   Qed.

(* two different choices of composition order are naturally isomorphic (strictly, in fact) *)
Definition if_associativity
  `{C1 : Category} `{C2 : Category} `{C3 : Category} `{C4 : Category}
  {Fobj1}(F1 : Functor C1 C2 Fobj1)
  {Fobj2}(F2 : Functor C2 C3 Fobj2)
  {Fobj3}(F3 : Functor C3 C4 Fobj3)
   : 
  ((F1 >>>> F2) >>>> F3) ≃ (F1 >>>> (F2 >>>> F3)).
  exists (fun A => iso_id (F3 (F2 (F1 A)))).
  abstract (intros;
            simpl;
            setoid_rewrite left_identity;
            setoid_rewrite right_identity;
            reflexivity).
  Defined.

Definition if_left_identity `{C1 : Category} `{C2 : Category} {Fobj1}(F1 : Functor C1 C2 Fobj1)  :  (functor_id _ >>>> F1) ≃ F1.
  exists (fun a => iso_id (F1 a)).
  abstract (intros; unfold functor_comp; simpl;
            setoid_rewrite left_identity;
            setoid_rewrite right_identity;
            reflexivity).
  Defined.

Definition if_right_identity `{C1 : Category} `{C2 : Category} {Fobj1}(F1 : Functor C1 C2 Fobj1)  :  (F1 >>>> functor_id _) ≃ F1.
  exists (fun a => iso_id (F1 a)).
  abstract (intros; unfold functor_comp; simpl;
            setoid_rewrite left_identity;
            setoid_rewrite right_identity;
            reflexivity).
  Defined.

Definition if_respects
  `{A : Category} `{B : Category}
  {F0obj}(F0 : Functor A B F0obj)
  {F1obj}(F1 : Functor A B F1obj)
  `{C : Category}
  {G0obj}(G0 : Functor B C G0obj)
  {G1obj}(G1 : Functor B C G1obj)
   :  (F0 ≃ F1) -> (G0 ≃ G1) -> ((F0 >>>> G0) ≃ (F1 >>>> G1)).
  intro phi.
  intro psi.
  destruct psi as [ psi_niso psi_comm ].
  destruct phi as [ phi_niso phi_comm ].
  exists (fun a => iso_comp ((@functors_preserve_isos _ _ _ _ _ _ _ G0) _ _ (phi_niso a)) (psi_niso (F1obj a))).
  abstract (intros; simpl;
            setoid_rewrite <- associativity;
            setoid_rewrite fmor_preserves_comp;
            setoid_rewrite <- phi_comm;
            setoid_rewrite <- fmor_preserves_comp;
            setoid_rewrite associativity;
            apply comp_respects; try reflexivity;
            apply psi_comm).
  Defined.

Section ni_prod_comp.
Require Import ProductCategories_ch1_6_1.
  Context
  `{C1 : Category} `{C2 : Category}
  `{D1 : Category} `{D2 : Category}
   {F1Obj}(F1 : @Functor _ _ C1 _ _ D1 F1Obj)
   {F2Obj}(F2 : @Functor _ _ C2 _ _ D2 F2Obj)
  `{E1 : Category} `{E2 : Category}
   {G1Obj}(G1 : @Functor _ _ D1 _ _ E1 G1Obj)
   {G2Obj}(G2 : @Functor _ _ D2 _ _ E2 G2Obj).

  Definition ni_prod_comp_iso A  :  (((F1 >>>> G1) **** (F2 >>>> G2)) A) ≅ (((F1 **** F2) >>>> (G1 **** G2)) A).
    unfold functor_fobj.
    unfold functor_product_fobj.
    simpl.
    apply iso_id.
    Defined.

  Lemma ni_prod_comp  :  (F1 >>>> G1) **** (F2 >>>> G2) <~~~> (F1 **** F2) >>>> (G1 **** G2).
    refine {| ni_iso := ni_prod_comp_iso |}.
    intros.
    destruct A.
    destruct B.
    simpl.
    setoid_rewrite left_identity.
    setoid_rewrite right_identity.
    split; reflexivity.
    Defined.
End ni_prod_comp.

