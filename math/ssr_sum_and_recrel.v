(**
和と漸化式
==================

2020_10_3 @suharahiromichi
*)

(**
# はじめに

ソースコードは以下にあります。

 *)

From mathcomp Require Import all_ssreflect.
Require Import Recdef.
Require Import Wf_nat.                      (* well_founded lt *)
Require Import ssromega.

(**
https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v

もダウンロードして同じディレクトリに置いて、coqc ssromega.v を実行し、
ssromega.vo ができていることを確認してください。
*)
     
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Recrel.

  Variables alpha beta gamma : nat.
  
(**
漸化式
*)  
  Fixpoint R_rel (n : nat) : nat :=
    if n is n'.+1 then
      R_rel n' + beta + gamma * n
    else
      alpha.

  Lemma R_rel_0 : R_rel 0 = alpha.
  Proof. done. Qed.
  
  Lemma R_rel_n (n : nat) :
    R_rel n.+1 = R_rel n + beta + gamma * n.+1.
  Proof. by rewrite {1}/R_rel. Qed.
  
(**
漸化式の解
*)  
  Definition R_sol (n : nat) : nat :=
    alpha + n * beta + (n^2 + n)./2 * gamma.

(**
2を掛けて2で割るともとにもどる。
*)  
  Lemma mul2K (n : nat) : n.*2./2 = n.
  Proof.
    by rewrite -muln2 -divn2 mulnK.
  Qed.
  
(**
通分のための前処理をする。
*)
  Lemma div_fract (n : nat) : n.+1^2 + n.+1 = (n^2 + n) + (n.+1).*2.
  Proof.
    rewrite -{1}addn1 sqrnD.
    rewrite -[in (n.+1).*2]mul2n.
    rewrite -[n.+1]addn1.
    rewrite -mulnn.
    rewrite exp1n.
      by ssromega.
  Qed.
  
(**
通分の条件を証明する。
*)
  Lemma odd_false (n : nat) : odd (n^2 + n) && odd (n.+1).*2 = false.
  Proof.
    apply: negbTE.
    rewrite negb_and.
    apply/orP/or_intror.
      by rewrite odd_double.
  Qed.
  
  Goal forall n, R_rel n = R_sol n.
  Proof.
    elim=> [| n IHn].
    - rewrite /R_rel /R_sol /=.
        by ssromega.
    - rewrite R_rel_n IHn /R_sol.
      (* 同類項をまとめる。 *)
      rewrite -[alpha + n * beta + (n ^ 2 + n)./2 * gamma + beta]addnAC.
      rewrite -[alpha + n * beta + beta]addnA.
      rewrite -[in LHS]addnA.
      
      (* 同類項をゴールに分ける。 *)
      congr (_ + _ + _).
      
      (* beta の項 *)
      + rewrite mulSn.
          by ssromega.
          
      (* gamma の項 *)
      + rewrite [gamma * n.+1]mulnC -[LHS]mulnDl.
        congr (_ * gamma).
        (* 通分の前処理をする。 *)
        rewrite -[n.+1 in LHS]mul2K.
        rewrite div_fract.
        (* /2 を通分する。先立って odd の条件を追加する。 *)
        rewrite -[LHS]add0n.
        have {1}-> : 0 = false by done.
        rewrite -{1}[false in LHS](odd_false n).
        rewrite -[LHS]halfD.

        (* 左辺 = 右辺 *)
        done.
  Qed.
End Recrel.

(**
# 参考文献

Knuth 他著、有沢他訳、「コンピュータの数学」 共立出版。第２章
*)

(* END *)
