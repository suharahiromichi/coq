(* Examples of type classes and Setoids *)

Set Implicit Arguments.
Require Import List.
Require Import ZArith.
Require Import Morphisms Relations.

Require Import coq_gitcrc_3_digest.
Require Import coq_gitcrc_3_7_digest.

Class EMonoid (A:Type) (E_eq :relation  A) (dot : A->A->A) (one : A) :=
  {
    E_rel :> Equivalence E_eq; 
    dot_proper :> Proper (E_eq ==> E_eq ==> E_eq) dot; 
    E_dot_assoc : forall x y z:A, E_eq (dot x (dot y z)) (dot (dot x y) z);
    E_one_left : forall x, E_eq (dot one  x) x;
    E_one_right : forall x, E_eq (dot x  one) x
  }.

Generalizable Variables A E_eq dot one.

Fixpoint Epower `{M: EMonoid } (a:A) (n:nat) :=
  match n with
    | 0%nat => one
    | S p => dot a (Epower a p)
  end.

Instance Route : EMonoid route_equiv (@app _) nil.
Proof.
  split.
  apply route_equiv_Equiv.
  apply app_route_Proper.
  intros x y z P;repeat rewrite route_compose; trivial.
  intros x P;repeat rewrite route_compose; trivial.
  intros x P;repeat rewrite route_compose; trivial.
Qed.

Program Instance Route' : EMonoid route_equiv (@app _) nil.
Next Obligation.
Proof.
  intros P; repeat rewrite route_compose; trivial.
Qed.
Next Obligation.
Proof.
  intros P; repeat rewrite route_compose; trivial.
Qed.
Next Obligation.
  intros P; repeat rewrite route_compose; trivial.
Qed.

Goal forall n, Epower (South::North::nil) n =r= nil.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn.
    route_eq_tac.
Qed.

Class Abelian_EMonoid `(M:EMonoid ) :=
  {
    Edot_comm : forall x y, E_eq (dot x  y)  (dot y  x)
  }.

(* END *)
