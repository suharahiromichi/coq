(**
# 第9回 タクティックの定義と利用/停止性証明 (2014/06/08)

http://qnighy.github.io/coqex2014/

## 課題44 (種別:C / 締め切り : 2014/06/29)

課題42で証明したlog関数に関する性質を証明せよ。
*)

Require Import ssreflect ssrbool ssrnat div eqtype.
Require Import Recdef.

(*
Require Import Arith.
Require Import Omega.
Require Import Recdef.
*)

Require Import Lt.

(*
 well_founded lt を示す定理が見つからない。
 これは、Coq'n art の一部
 *)
Theorem lt_Acc : forall n:nat, Acc lt n.
Proof.
 induction n.
 split; intros p H; inversion H.
 split. 
 intros y H0.
 case (le_lt_or_eq _ _ H0).
 intro; apply Acc_inv with n; auto with arith.
 intro e; injection e; intro e1; rewrite e1; assumption. 
Qed.

Function log (n:nat) {wf lt n} :=
  match n with
    | 0 => 0
    | 1 => 0
    | n => (log (n %/ 2)).+1
  end.
Proof.
  + move=> n2 n1 n Hn1 Hn2.
    rewrite -!Hn2.
    apply/leP.
    apply ltn_Pdiv.
      - by [].
      - by rewrite Hn2.
  + rewrite /well_founded.
    by apply lt_Acc.
Qed.

(* ここまでは課題42 *)

Fixpoint pow (n:nat) :=
  match n with
    | O => 1
    | n'.+1 => 2 * pow n'
  end.

Lemma pown1_2pown : forall n, pow n.+1 = 2 * pow n.
Proof.
  by [].
Qed.

Lemma mn2__2mn : forall n m, (m <= n %/ 2) = (2 * m <= n).
Proof.
  move=> n m.
  rewrite leq_divRL.
  + by rewrite -mulnC.
  + by [].
Qed.

Lemma mn2_2mn : forall n m, m <= n %/ 2 -> 2 * m <= n.
Proof.
  move=> n m H.
  have Hmn : forall n m, (m <= n %/ 2) = (2 * m <= n)
                         by apply mn2__2mn.
  case Hmn.
  by [].
Qed.

Lemma np2d2_nd2p1 : forall n, (n + 2) %/ 2 = (n %/ 2) + 1.
Proof.
  move=> n.
  rewrite divnDr.
  have H : 2 %/ 2 = 1 by rewrite //.
  + by rewrite H.                                 
  + by [].
Qed.

Lemma log_pow_lb: forall n, 1 <= n -> pow (log n) <= n.
Proof.
  move=> n H.
  functional induction (log n).
  + by [].                                  (* pow 0 <= 0 *)
  + by [].                                  (* pow 0 <= 1 *)
  + rewrite pown1_2pown.
    apply mn2_2mn.
    apply IHn0.
    destruct n.
    - inversion H.
    - destruct n.
      * inversion y.
      * rewrite -addn2.
        rewrite np2d2_nd2p1.
        apply ltn_addl.
        by [].
Qed.
  
(**
ヒント

functional inductionタクティックを使うと、Functionで定義した計算の構造に従う帰納法を行うことができます。
*)

(* END *)
