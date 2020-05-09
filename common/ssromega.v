From mathcomp Require Import all_ssreflect.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing All. *)

(* https://github.com/affeldt-aist/seplog/blob/master/lib/ssrnat_ext.v *)

Ltac ssromega :=
  (repeat ssrnat2coqnat_hypo ;
   ssrnat2coqnat_goal ;
   omega)
with ssrnat2coqnat_hypo :=
  match goal with
    | H : context [?L < ?R] |- _ => move/ltP: H => H
    | H : context [?L <= ?R] |- _ => move/leP: H => H
    | H : context [?L < ?M < ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M < ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M <= ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [?L + ?R] |- _ => rewrite <- plusE in H
    | H : context [?L * ?R] |- _ => rewrite <- multE in H
    | H : context [?L - ?R] |- _ => rewrite <- minusE in H
    | H : ?x == _ |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ == ?x |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ != ?x |- _ => match type of x with nat => move/eqP in H end
  end
with ssrnat2coqnat_goal :=
  rewrite -?plusE -?minusE -?multE;
  match goal with
    | |- is_true (_ < _)%nat => apply/ltP
    | |- is_true (_ <= _)%nat => apply/leP
    | |- is_true (_ && _) => apply/andP; split; ssromega
    | |- is_true (?x != _) => match type of x with nat => apply/eqP end
    | |- is_true (_ != ?x) => match type of x with nat => apply/eqP end
    | |- is_true (?x == _) => match type of x with nat => apply/eqP end
    | |- is_true (_ == ?x) => match type of x with nat => apply/eqP end
    | |- _ /\ _ => split; ssromega
    | |- _ \/ _ => (left; ssromega) || (right; ssromega)
    | |- _ => idtac
  end.

(* Sample *)
Goal forall x y : nat, x + 4 - 2 > y + 4 -> (x + 2) + 2 >= y + 6.
Proof.
  move=> x y H.
    by ssromega.
Qed.

(* END *)
