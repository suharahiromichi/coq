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

(* FRAP の linear_arithmetic *)
(* min と max を扱う。 *)

Ltac linear_arithmetic' :=
  intros;
  repeat match goal with
         | [ |- context[maxn ?a ?b] ] =>
           rewrite {1}/maxn; case: (leqP b a); intros

         | [ H : context[maxn ?a ?b] |- _ ] =>
           let H' := fresh in
           rewrite {1}/maxn in H; case: (leqP b a) => H'; try rewrite H' in H

         | [ |- context[minn ?a ?b] ] =>
           rewrite {1}/minn; case: (leqP b a); intros

         | [ H : context[minn ?a ?b] |- _ ] =>
           let H' := fresh in
           rewrite {1}/minn in H; case: (leqP b a) => H';
           try (rewrite leqNgt in H'; move/Bool.negb_true_iff in H'; rewrite H' in H)

         | _ => idtac
         end.
(* case H' : (a < b) の H' が展開できないため、それを使うのを避ける。 *)
(* destruct (a < b) eqn:H' としてもよい。 *)
(*
           let H' := fresh in
           rewrite {1}/maxn; destruct (a < b) eqn: H'; intros
*)

Ltac linear_arithmetic :=
  linear_arithmetic';
  try ssromega;
  rewrite //=.

(* END *)
