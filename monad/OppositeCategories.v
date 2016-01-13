(******************************************************************************)
(* Chapter 1.6.2: Opposite Categories                                         *)
(******************************************************************************)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import finset fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Notations.
Require Import Categories.
Require Import Functors.
Require Import Isomorphisms.

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
  move=> f' g' H'.
  simpl.
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
  apply associativity.
Defined.


(* Notation "dual C" := (Opposite C)  : category_scope. *)

(* every functor between two categories determines a functor between their opposites *)
Definition func_op `(F : Functor (c1 := c1) (c2 := c2) (fobj := fobj)) :
  Functor (Opposite c1) (Opposite c2) fobj.
  apply (@Build_Functor _ _ (Opposite c1) _ _ (Oppsite c2) fobj (fun a b f => fmor F f)).
  abstract (intros; apply (@fmor_respects _ _ _ _ _ _ _ F _ _ f f' H)).
  abstract (intros; apply (@fmor_preserves_id _ _ _ _ _ _ _ F a)).
  abstract (intros; apply (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ g _ f)).
  Defined.

(* we could do this by simply showing that (Opposite (Opposite C)) is isomorphic to C, but Coq distinguishes between
 * two categories being *equal* versus merely isomorphic, so it's handy to be able to do this *)
Definition func_opop `{c1:Category}`{c2:Category}{fobj}(F:Functor (Opposite c1) (Opposite c2) fobj) : Functor c1 c2 fobj.
  apply (@Build_Functor _ _ c1 _ _ c2 fobj (fun a b f => fmor F f)).
  abstract (intros; apply (@fmor_respects _ _ _ _ _ _ _ F _ _ f f' H)).
  abstract (intros; apply (@fmor_preserves_id _ _ _ _ _ _ _ F a)).
  abstract (intros; apply (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ g _ f)).
  Defined.

Definition func_op1 `{c1:Category}`{c2:Category}{fobj}(F:Functor (Opposite c1) c2 fobj) : Functor c1 (Opposite c2) fobj.
  apply (@Build_Functor _ _ c1 _ _ (Opposite c2) fobj (fun a b f => fmor F f)).
  abstract (intros; apply (@fmor_respects _ _ _ _ _ _ _ F _ _ f f' H)).
  abstract (intros; apply (@fmor_preserves_id _ _ _ _ _ _ _ F a)).
  abstract (intros; apply (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ g _ f)).
  Defined.

Definition func_op2 `{c1:Category}`{c2:Category}{fobj}(F:Functor c1 (Opposite c2) fobj) : Functor (Opposite c1) c2 fobj.
  apply (@Build_Functor _ _ (Opposite c1) _ _ c2 fobj (fun a b f => fmor F f)).
  abstract (intros; apply (@fmor_respects _ _ _ _ _ _ _ F _ _ f f' H)).
  abstract (intros; apply (@fmor_preserves_id _ _ _ _ _ _ _ F a)).
  abstract (intros; apply (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ g _ f)).
  Defined.

