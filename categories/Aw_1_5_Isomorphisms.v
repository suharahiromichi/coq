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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Morphisms.                   (* coq standard libs. *)
Require Import Aw_0_Notations.              (* same dir. *)
Require Import Aw_1_3_Categories.           (* same dir. *)
Require Import Aw_1_4_Functors.             (* same dir. *)

(* 圏Cにおいて、同型射 f : a ~> b が存在するとき、a と b は同型である。 *)
(* 同型射とは、g \\o f === iid かつ f \\o g === iid なる f *)
Class Isomorphism `{C : Category} {a b : C} (f : a ~> b) (g : b ~> a) : Prop :=
  {
    iso_cmp1  : g \\o f === iid;            (* iid a *)
    iso_cmp2  : f \\o g === iid             (* iid b *)
  }.
(* TO DO: show isos are unique when they exist *)

(* f と g をメンバで定義した版 *)
Class Isomorphic `{C : Category} (a b : C) :=
  {
    iso_forward  :  a ~> b;
    iso_backward :  b ~> a;
    iso_comp1    :  iso_backward \\o iso_forward === iid; (* iid a *)
    iso_comp2    :  iso_forward \\o iso_backward === iid  (* iid b *)
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
  - by apply iso_comp2.
  - by apply iso_comp1.
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
  Check @Build_Isomorphic _ _ C a a iid iid.
  apply (@Build_Isomorphic _ _ C a a iid iid).
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
  Check iso_comp1 i1 : iso_backward i1 \\o #i1 === iid.
  Check iso_comp2 i1 : #i1 \\o iso_backward i1 === iid.
  Check iso_comp1 i2 : iso_backward i2 \\o #i2 === iid.
  Check iso_comp2 i2 : #i2 \\o iso_backward i2 === iid.

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

(* 関手は同型を保存する。 *)
Definition functors_preserve_isos `{C1 : Category} `{C2 : Category} {Fo : C1 -> C2}
           (F : Functor Fo) {a b : C1} (i : Isomorphic a b) : Isomorphic (F a) (F b).
Proof.
  (* 圏C1を関手で写した先の圏C2、C2の同型を作る。 *)
  Check F \ (iso_forward i) : F a ~> F b.
  Check F \ #i : F a ~> F b.
  Check F \ (iso_backward i) : F b ~> F a.
  Check {| iso_forward  := F \ (iso_forward  i);
           iso_backward := F \ (iso_backward i)
        |}.
  Check (@Build_Isomorphic).
  Check (@Build_Isomorphic Obj0 Hom0 C2 (F a) (F b)
                           (F \ (# i))
                           (F \ (iso_backward i))).
  Check (@Build_Isomorphic _ _ _ (F a) (F b)
                           (F \ (# i))
                           (F \ (iso_backward i))).
  (* Standard Coq の refine は、SSReflect の apply: である。 *)
  refine {| iso_forward  := F \ (iso_forward  i);
            iso_backward := F \ (iso_backward i)
         |}.
  Undo 1.
  apply: {| iso_forward  := F \ (iso_forward  i);
            iso_backward := F \ (iso_backward i)
         |}.
  Undo 1.
  apply (@Build_Isomorphic _ _ _ _ _
                           (F \ (# i))
                           (F \ (iso_backward i))).
  (* F \ iso_backward i \\o F \ #i === iid *)
  - rewrite fmor_preserves_comp.
    rewrite iso_comp1.
    apply fmor_preserves_id.
  (* F \ #i \\o F \ iso_backward i === iid *)
  - rewrite fmor_preserves_comp.
    rewrite iso_comp2.
    apply fmor_preserves_id.
Defined.

(* 圏Cの対象b,aが同型である（同型射 b ~> c がある）とき、
   圏Cの射f : b ~> c と、射g : a ~> c の関係を示す。
 *)
Lemma iso_shift_right `{C : Category} {a b c : C}
      (f : b ~> c) (g : a ~> c) (i : Isomorphic b a) :
  f \\o #i⁻¹ === g -> f === g \\o #i.
Proof.
  move=> H.
  rewrite -H associativity iso_comp1 right_identity.
  reflexivity.
Qed.  

Lemma iso_shift_right' `{C : Category} {a b c : C}
      (f : b ~> c) (g : a ~> c) (i : Isomorphic a b) :
  f \\o #i === g -> f === g \\o #i⁻¹.
Proof.
  move=> H.
  rewrite -H.
  rewrite associativity.                    (* assoc の定義がオリジナルと異なる。 *)
  rewrite iso_comp2 right_identity.         (* あとは、少し証明が変わる。 *)
  reflexivity.
Qed.  

Lemma iso_shift_left `{C : Category} {a b c : C}
      (f : a ~> b) (g : a ~> c) (i : Isomorphic c b) :
  #i⁻¹ \\o f === g -> f === #i \\o g.
Proof.
  move=> H.
  rewrite -H -associativity iso_comp2 left_identity.
  reflexivity.
Qed.

Lemma iso_shift_left' `{C : Category} {a b c : C}
      (f : a ~> b) (g : a ~> c) (i : Isomorphic b c) :
  #i \\o f === g -> f === #i⁻¹ \\o g.
Proof.
  move=> H.
  rewrite -H -associativity iso_comp1 left_identity.
  reflexivity.
Qed.  

(* 圏Cの対象aとbに対して、a,bの同型（同型射 a ~> b）が同じなら、
b,aの同型（同型射 b ~> a）も同じである。 *)
Lemma isos_forward_equal_then_backward_equal `{C : Category} {a b : C}
      (i1 i2 : Isomorphic a b)  :  #i1 === #i2 ->  #i1⁻¹ === #i2⁻¹.
Proof.
  move=> H.
  rewrite -[#i1 ⁻¹]left_identity.
  rewrite -(iso_comp1 i2).
  rewrite associativity.
  rewrite -H.
  rewrite (iso_comp2 i1).
  rewrite right_identity.
  rewrite /=.
  reflexivity.
Qed.

(* 圏Cの対象aとbに対して、a,bの同型（同型射 a ~> b）の逆の逆は同じ *)
Lemma iso_inv_inv `{C : Category} {a b : C} (i : Isomorphic a b) :
  #(i⁻¹)⁻¹ === #i.
Proof.
  rewrite /iso_inv /=.
  reflexivity.
Qed.

(* the next four lemmas are handy for setoid_rewrite; they let you
avoid having to get the associativities right *)

Lemma iso_comp2_right  `{C : Category} {a b c : C} (i : Isomorphic a b)  (g : b ~> c) :
  g \\o iso_forward i \\o iso_backward i === g.
Proof.
  rewrite associativity.
  rewrite iso_comp2.
  rewrite right_identity.
  reflexivity.
Qed.

Lemma iso_comp2_left `{C : Category} {a b c : C} (i : Isomorphic a b)  (g : c ~> b) :
  iso_forward i \\o (iso_backward i \\o g)  === g.
Proof.
  rewrite -associativity.
  rewrite iso_comp2.
  rewrite left_identity.
  reflexivity.
Qed.

Lemma iso_comp1_right `{C : Category} {a b c : C} (i : Isomorphic a b)  (g : a ~> c) :
  g \\o iso_backward i \\o iso_forward i === g.
Proof.
  rewrite associativity.
  rewrite iso_comp1.
  rewrite right_identity.
  reflexivity.
Qed.

Lemma iso_comp1_left `{C : Category} {a b c : C} (i : Isomorphic a b)  (g : c ~> a) :
  iso_backward i \\o (iso_forward i \\o g)  === g.
Proof.
  rewrite -associativity.
  rewrite iso_comp1.
  rewrite left_identity.
  reflexivity.
Qed.

(* END *)
