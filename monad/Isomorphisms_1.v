(******************************************************************************)
(* Chapter 1.5: Isomorphisms                                                  *)
(******************************************************************************)

(*
(0)
同じディレクトリにある Categories.v と Functor.v を使う。

(1) ベースライン
http://www.megacz.com/berkeley/coq-categories/
これをもとに改変。Instance ... Proper を使うようにした。
 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import finset fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Morphisms.                   (* coq standard libs. *)
Require Import Notations.                   (* same dir. *)
Require Import Categories.                  (* same dir. *)
Require Import Functors.                    (* same dir. *)

(* 圏Cにおいて、同型射 f : a ~> b が存在するとき、a と b は同型である。 *)
(* 同型射とは、g \\o f === id かつ f \\o g === id なる f *)
Class Isomorphism `{C : Category} {a b : C} (f : a ~> b) (g : b ~> a) : Prop :=
  {
    iso_cmp1  : g \\o f === id;             (* id a *)
    iso_cmp2  : f \\o g === id              (* id b *)
  }.
(* TO DO: show isos are unique when they exist *)

(* f と g をメンバで定義した版 *)
Class Isomorphic `{C : Category} (a b : C) :=
  {
    iso_forward  :  a ~> b;
    iso_backward :  b ~> a;
    iso_comp1    :  iso_backward \\o iso_forward === id; (* id a *)
    iso_comp2    :  iso_forward \\o iso_backward === id  (* id b *)
(* TO DO: merge this with Isomorphism *)
}.
(* 同型射 f は、ひとつの同型(な関係にあるaとb)を与えないと決まらない。
   Isomorphic a b をexplicitに与えるようにする。 *)
Check @iso_forward : ∀Obj Hom C a b _, a ~> b.
Check iso_forward : _ ~> _.
Arguments iso_forward  {Obj Hom C a b} i : rename.
Arguments iso_backward {Obj Hom C a b} i : rename.
Arguments iso_comp1    {Obj Hom C a b} i : rename.
Arguments iso_comp2    {Obj Hom C a b} i : rename.
Check iso_forward _ : _ ~> _.                 (* 最初の _ は、Isomorphic a b *)
Check iso_forward : Isomorphic _ _ -> _ ~> _. (* _ は、圏Cの対象 a b *)

Notation "a ≅ b" := (Isomorphic a b) : isomorphism_scope.
(* the sharp symbol "casts" an isomorphism to the morphism in the forward direction *)
Notation "# f" := (iso_forward f) : isomorphism_scope.
Open Scope isomorphism_scope.


(* 同型a,bに対して、同型b,aを求めることができる。 *)
(* aに対してbが同型なら、bに対してaも同型である。 *)
(* the inverse of an isomorphism is an isomorphism *)
Definition iso_inv `{C : Category} (a b : C) (iso : Isomorphic a b) : Isomorphic b a.
Proof.
  Check iso_backward.
  Check @Build_Isomorphic _ _ _ _ _ (iso_backward iso) (iso_forward iso).
  apply (@Build_Isomorphic _ _ _ _ _ (iso_backward iso) (iso_forward iso)).
  - now apply iso_comp2.
  - now apply iso_comp1.
Defined.
Check @iso_inv : ∀Obj Hom C a b _, b ≅ a.
Arguments iso_inv {Obj Hom C a b} f : rename.
Check iso_inv _ : _ ≅ _.                    (* 最初の _ は a ≅ b *)
Check iso_inv : _ ≅ _ -> _ ≅ _.             (* _ は、圏Cの対象 a b *)
Notation "f '⁻¹'" := (iso_inv f) : isomorphism_scope.

(* 同型a,a *)
(* aとaは同型である。 *)
(* identity maps are isomorphisms *)
Definition iso_id `{C : Category} (a : C) : Isomorphic a a.
Proof.
  Check @Build_Isomorphic _ _ C a a id id.
  apply (@Build_Isomorphic _ _ C a a id id).
  now rewrite left_identity.
  now rewrite left_identity.
Defined.
Check @iso_id.
Arguments iso_id {Obj Hom C a} : rename.
Check iso_id : _ ≅ _.                       (* _ は、圏Cの対象a *)

(* 同型a,b と 同型b,c なら、同型a,c *)
(* the composition of two isomorphisms is an isomorphism *)
Definition iso_comp `{C : Category} {a b c : C}
           (i1 : Isomorphic a b) (i2 : Isomorphic b c) : Isomorphic a c.
Proof.
  Check #i1 : a ~> b.                       (* iso_forward i1 *)
  Check #i2 : b ~> c.                       (* iso_forward i2 *)
  Check #i2 \\o #i1 : a ~> c.
  Check #i1⁻¹ : b ~> a.                     (* iso_inv (iso_forward i1) *)
  Check #i2⁻¹ : c ~> b.                     (* iso_inv (iso_forward i2) *)
  Check iso_comp1 i1 : iso_backward i1 \\o #i1 === id.
  Check iso_comp2 i1 : #i1 \\o iso_backward i1 === id.
  Check iso_comp1 i2 : iso_backward i2 \\o #i2 === id.
  Check iso_comp2 i2 : #i2 \\o iso_backward i2 === id.

  Check (@Build_Isomorphic _ _ C a c (#i2 \\o #i1) (#i1⁻¹ \\o #i2⁻¹)).
  apply (@Build_Isomorphic _ _ C a c (#i2 \\o #i1) (#i1⁻¹ \\o #i2⁻¹)).
  - rewrite juggle3 (iso_comp1 i2).
    rewrite associativity left_identity (iso_comp1 i1).
    reflexivity.
  - rewrite juggle3 (iso_comp2 i1).
    rewrite associativity left_identity (iso_comp2 i2).
    reflexivity.
Defined.
Check @iso_comp : ∀Obj Hom C a b c _ _, a ≅ c.
Check iso_comp _ _ : _ ≅ _.
Arguments iso_comp {Obj Hom C} a b c i1 i2 : rename.
Check iso_comp : ∀a b c _ _, a ≅ c.
Notation "a >>≅>> b" := (iso_comp a b).

(* ここまで *)

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

Lemma iso_shift_right `{C:Category} : forall {a b c:C}(f:b~>c)(g:a~>c)(i:Isomorphic b a), #i⁻¹ \\o f ~~ g -> f ~~ #i \\o g.
  intros.
  setoid_rewrite <- H.
  setoid_rewrite <- associativity.
  setoid_rewrite iso_comp1.
  symmetry.
  apply left_identity.
  Qed.  

Lemma iso_shift_right' `{C:Category} : forall {a b c:C}(f:b~>c)(g:a~>c)(i:Isomorphic a b), #i \\o f ~~ g -> f ~~ #i⁻¹ \\o g.
  intros.
  setoid_rewrite <- H.
  setoid_rewrite <- associativity.
  setoid_rewrite iso_comp1.
  symmetry.
  apply left_identity.
  Qed.  

Lemma iso_shift_left `{C:Category} : forall {a b c:C}(f:a~>b)(g:a~>c)(i:Isomorphic c b), f \\o #i⁻¹ ~~ g -> f ~~ g \\o #i.
  intros.
  setoid_rewrite <- H.
  setoid_rewrite associativity.
  setoid_rewrite iso_comp1.
  symmetry.
  apply right_identity.
  Qed.  

Lemma iso_shift_left' `{C:Category} : forall {a b c:C}(f:a~>b)(g:a~>c)(i:Isomorphic b c), f \\o #i ~~ g -> f ~~ g \\o #i⁻¹.
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
Lemma iso_comp2_right : forall `{C:Category}{a b}(i:a≅b) c (g:b~>c), iso_backward i \\o (iso_forward i \\o g) ~~ g.
  intros.
  setoid_rewrite <- associativity.
  setoid_rewrite iso_comp2.
  apply left_identity.
  Qed.

Lemma iso_comp2_left : forall `{C:Category}{a b}(i:a≅b) c (g:c~>b), (g \\o iso_backward i) \\o iso_forward i ~~ g.
  intros.
  setoid_rewrite associativity.
  setoid_rewrite iso_comp2.
  apply right_identity.
  Qed.

Lemma iso_comp1_right : forall `{C:Category}{a b}(i:a≅b) c (g:a~>c), iso_forward i \\o (iso_backward i \\o g) ~~ g.
  intros.
  setoid_rewrite <- associativity.
  setoid_rewrite iso_comp1.
  apply left_identity.
  Qed.

Lemma iso_comp1_left : forall `{C:Category}{a b}(i:a≅b) c (g:c~>a), (g \\o iso_forward i) \\o iso_backward i ~~ g.
  intros.
  setoid_rewrite associativity.
  setoid_rewrite iso_comp1.
  apply right_identity.
  Qed.
