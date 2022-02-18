From mathcomp Require Import all_ssreflect.
Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing All. *)

(**
ssromega を使えるようにする手順；
1. カレントディでクトリに置く場合：
(1) coqc ssromega.v
(2) Require Import ssromega. で読み込む。

2. パスを通す場合：
(1) ~/.coqrc に以下の行を追加する。
Add LoadPath "~/WORK/coq/common" as common.
(2) ~/WORK/coq/common/ の下で以下を実行する。
coq_makefile -R . common ssromega.v > Makefile
(3) make clean; make
ssromega.vo ができている。
(4) From common Require Import ssromega. で読み込む。
*)

(* https://github.com/affeldt-aist/seplog/blob/master/lib/ssrnat_ext.v *)

Ltac ssromega :=
  (repeat ssrnat2coqnat_hypo ;
   ssrnat2coqnat_goal ;
   lia)
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
