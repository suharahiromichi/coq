(******************************************************************************)
(* Chapter 1.6.2: Opposite Categories                                         *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Aw_0_Notations.
Require Import Aw_1_3_Categories.
Require Import Aw_1_4_Functors.
Require Import Aw_1_5_Isomorphisms.

Check @Category.

Generalizable Variables Obj Hom a b c d.

Lemma ref_eqv `{C : Category} `(f : a ~> b) `(g : a ~> b) :
  f === g -> g === f.
Proof.
  move=> H.
  rewrite H.
  reflexivity.
Qed.

Program Instance Opposite `(C : @Category Obj Hom) : @Category Obj (fun x y => Hom y x).
Obligation 1.                               (* Hom a a *)
Proof.
    by apply: id.
Defined.
Obligation 2.                               (* Hom c a *)
Proof.
  Check @comp _ _ C c b a X0 X : Hom c a.
    by apply: (@comp _ _ C c b a X0 X : Hom c a).
Defined.
Obligation 3.
Proof.
  rewrite /Opposite_obligation_2 /=.
  move=> f g H.
  move=> f' g' H' /=.
  Check @comp_respects Obj Hom C c b a f' g' H' f g H.
    by apply (@comp_respects Obj Hom C c b a f' g' H' f g H).
Defined.
Obligation 4.
  rewrite /Opposite_obligation_1 /Opposite_obligation_2 /=.
  Check right_identity.
    by apply right_identity.
Defined.
Obligation 5.
  rewrite /Opposite_obligation_1 /Opposite_obligation_2 /=.
    by apply left_identity.
Defined.
Obligation 6.
  rewrite /Opposite_obligation_2 /=.
  apply ref_eqv.
    by apply associativity.
Defined.


(* Notation "dual C" := (Opposite C)  : category_scope. *)

Generalizable Variables C D Fobj.

(* every functor between two categories determines a functor between their opposites *)
(* 双対の圏どうしの関手を定義する。 *)
Program Instance func_op `(F : @Functor _ _ C _ _ D Fobj) :
  @Functor _ _ (Opposite C) _ _ (Opposite D) Fobj :=
  {|
    fmor := (fun a b f => fmor F f)
  |}.
Obligation 2.
Proof.
  done.
Defined.
Obligation 3.
Proof.
  done.
Defined.

(* we could do this by simply showing that (Opposite (Opposite C)) is
 isomorphic to C, but Coq distinguishes between two categories being
 *equal* versus merely isomorphic, so it's handy to be able to do
 this *)

Program Instance func_opop `(F : @Functor _ _ (Opposite C) _ _ (Opposite D) Fobj) :
  @Functor _ _ C _ _ D Fobj :=
  {|
    fmor := (fun a b f => fmor F f)
  |}.
Obligation 2.
Proof.
  done.
Defined.
Obligation 3.
Proof.
  done.
Defined.

Program Instance func_op1 `(F : @Functor _ _ (Opposite C) _ _ D Fobj) :
  @Functor _ _ C _ _ (Opposite D) Fobj :=
  {|
    fmor := (fun a b f => fmor F f)
  |}.
Obligation 2.
Proof.
  done.
Defined.
Obligation 3.
Proof.
  done.
Defined.

Program Instance func_op2 `(F : @Functor _ _ C _ _ (Opposite D) Fobj) :
  @Functor _ _ (Opposite C) _ _ D Fobj :=
  {|
    fmor := (fun a b f => fmor F f)
  |}.
Obligation 2.
Proof.
  done.
Defined.
Obligation 3.
Proof.
  done.
Defined.

(* END *)
