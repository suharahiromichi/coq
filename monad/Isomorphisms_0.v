Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.

(******************************************************************************)
(* Chapter 1.5: Isomorphisms                                                  *)
(******************************************************************************)

Class Isomorphism `{C:Category}{a b:C}(f:a~>b)(g:b~>a) : Prop :=
{ iso_cmp1  : f >>> g ~~ id a
; iso_cmp2  : g >>> f ~~ id b
}.
(* TO DO: show isos are unique when they exist *)

Class Isomorphic
`{ C           :  Category                                   }
( a b          :  C                                          ) :=
{ iso_forward  :  a~>b
; iso_backward :  b~>a
; iso_comp1    :  iso_forward >>> iso_backward ~~ id a
; iso_comp2    :  iso_backward >>> iso_forward ~~ id b
(* TO DO: merge this with Isomorphism *)
}.
Implicit Arguments iso_forward  [ C a b Ob Hom ].
Implicit Arguments iso_backward [ C a b Ob Hom ].
Implicit Arguments iso_comp1    [ C a b Ob Hom ].
Implicit Arguments iso_comp2    [ C a b Ob Hom ].
Notation "a ≅ b" := (Isomorphic a b)    : isomorphism_scope.
(* the sharp symbol "casts" an isomorphism to the morphism in the forward direction *)
Notation "# f" := (@iso_forward _ _ _ _ _ f) : isomorphism_scope.
Open Scope isomorphism_scope.

(* the inverse of an isomorphism is an isomorphism *)
Definition iso_inv `{C:Category}(a b:C)(is:Isomorphic a b) : Isomorphic b a.
  intros; apply (Build_Isomorphic _ _ _ _ _ (iso_backward _) (iso_forward _)); 
  [ apply iso_comp2 | apply iso_comp1 ].
  Defined.
Notation "f '⁻¹'" := (@iso_inv _ _ _ _ _ f) : isomorphism_scope.

(* identity maps are isomorphisms *)
Definition iso_id `{C:Category}(A:C) : Isomorphic A A.
  intros; apply (Build_Isomorphic _ _ C A A (id A) (id A)); auto.
  Defined.

(* the composition of two isomorphisms is an isomorphism *)
Definition iso_comp `{C:Category}{a b c:C}(i1:Isomorphic a b)(i2:Isomorphic b c) : Isomorphic a c.
  intros; apply (@Build_Isomorphic _ _ C a c (#i1 >>> #i2) (#i2⁻¹ >>> #i1⁻¹));
    setoid_rewrite juggle3;
    [ setoid_rewrite (iso_comp1 i2) | setoid_rewrite (iso_comp2 i1) ];
    setoid_rewrite right_identity;
    [ setoid_rewrite (iso_comp1 i1) | setoid_rewrite (iso_comp2 i2) ];
    reflexivity.
  Defined.
Notation "a >>≅>> b" := (iso_comp a b).

Definition functors_preserve_isos `{C1:Category}`{C2:Category}{Fo}(F:Functor C1 C2 Fo){a b:C1}(i:Isomorphic a b)
  : Isomorphic (F a) (F b).
  refine {| iso_forward  := F \ (iso_forward  i)
          ; iso_backward := F \ (iso_backward i)
          |}.
  setoid_rewrite fmor_preserves_comp.
    setoid_rewrite iso_comp1.
    apply fmor_preserves_id.
  setoid_rewrite fmor_preserves_comp.
    setoid_rewrite iso_comp2.
    apply fmor_preserves_id.
  Defined.

Lemma iso_shift_right `{C:Category} : forall {a b c:C}(f:b~>c)(g:a~>c)(i:Isomorphic b a), #i⁻¹ >>> f ~~ g -> f ~~ #i >>> g.
  intros.
  setoid_rewrite <- H.
  setoid_rewrite <- associativity.
  setoid_rewrite iso_comp1.
  symmetry.
  apply left_identity.
  Qed.  

Lemma iso_shift_right' `{C:Category} : forall {a b c:C}(f:b~>c)(g:a~>c)(i:Isomorphic a b), #i >>> f ~~ g -> f ~~ #i⁻¹ >>> g.
  intros.
  setoid_rewrite <- H.
  setoid_rewrite <- associativity.
  setoid_rewrite iso_comp1.
  symmetry.
  apply left_identity.
  Qed.  

Lemma iso_shift_left `{C:Category} : forall {a b c:C}(f:a~>b)(g:a~>c)(i:Isomorphic c b), f >>> #i⁻¹ ~~ g -> f ~~ g >>> #i.
  intros.
  setoid_rewrite <- H.
  setoid_rewrite associativity.
  setoid_rewrite iso_comp1.
  symmetry.
  apply right_identity.
  Qed.  

Lemma iso_shift_left' `{C:Category} : forall {a b c:C}(f:a~>b)(g:a~>c)(i:Isomorphic b c), f >>> #i ~~ g -> f ~~ g >>> #i⁻¹.
  intros.
  setoid_rewrite <- H.
  setoid_rewrite associativity.
  setoid_rewrite iso_comp1.
  symmetry.
  apply right_identity.
  Qed.  

Lemma isos_forward_equal_then_backward_equal `{C:Category}{a}{b}(i1 i2:a ≅ b) : #i1 ~~ #i2 ->  #i1⁻¹ ~~ #i2⁻¹.
  intro H.
  setoid_rewrite <- left_identity at 1.
  setoid_rewrite <- (iso_comp2 i2).
  setoid_rewrite associativity.
  setoid_rewrite <- H.
  setoid_rewrite iso_comp1.
  setoid_rewrite right_identity.
  reflexivity.
  Qed.

Lemma iso_inv_inv `{C:Category}{a}{b}(i:a ≅ b) : #(i⁻¹)⁻¹ ~~ #i.
  unfold iso_inv; simpl.
  reflexivity.
  Qed.

(* the next four lemmas are handy for setoid_rewrite; they let you avoid having to get the associativities right *)
Lemma iso_comp2_right : forall `{C:Category}{a b}(i:a≅b) c (g:b~>c), iso_backward i >>> (iso_forward i >>> g) ~~ g.
  intros.
  setoid_rewrite <- associativity.
  setoid_rewrite iso_comp2.
  apply left_identity.
  Qed.

Lemma iso_comp2_left : forall `{C:Category}{a b}(i:a≅b) c (g:c~>b), (g >>> iso_backward i) >>> iso_forward i ~~ g.
  intros.
  setoid_rewrite associativity.
  setoid_rewrite iso_comp2.
  apply right_identity.
  Qed.

Lemma iso_comp1_right : forall `{C:Category}{a b}(i:a≅b) c (g:a~>c), iso_forward i >>> (iso_backward i >>> g) ~~ g.
  intros.
  setoid_rewrite <- associativity.
  setoid_rewrite iso_comp1.
  apply left_identity.
  Qed.

Lemma iso_comp1_left : forall `{C:Category}{a b}(i:a≅b) c (g:c~>a), (g >>> iso_forward i) >>> iso_backward i ~~ g.
  intros.
  setoid_rewrite associativity.
  setoid_rewrite iso_comp1.
  apply right_identity.
  Qed.
