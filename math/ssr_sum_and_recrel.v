(**
総和と漸化式
==================

2020_10_3 @suharahiromichi
*)

(**
# はじめに

ソースコードは以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_sum_and_recrel.v
 *)

From mathcomp Require Import all_ssreflect.
Require Import Recdef.
Require Import Wf_nat.                      (* well_founded lt *)
From common Require Import ssromega.
From common Require Import ssrsumop.

(**
https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v

と

https://github.com/suharahiromichi/coq/blob/master/common/ssrsumop.v

もダウンロードして同じディレクトリに置いて、coqc ssromega.v を実行し、
ssromega.vo ができていることを確認してください。
*)
     
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Recrel.

  Variable alpha beta gamma : nat.
  
(**
漸化式 式(2.7)
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
漸化式の解 式(2.8)
*)  
  Definition R_sol (n : nat) : nat :=
    alpha + n * beta + (n^2 + n)./2 * gamma.

(**
総和の式
 *)
  Definition R_sum (n : nat) : nat :=
    \sum_(1 <= i < n.+1) (beta + gamma * i) + alpha.

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
  
  (* 共通の数式の証明 *)
  Lemma alpha_beta_gamma (n : nat) :
    alpha + n * beta + (n ^ 2 + n)./2 * gamma + beta + gamma * n.+1 =
    alpha + n.+1 * beta + (n.+1 ^ 2 + n.+1)./2 * gamma.
  Proof.
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
  
(**
漸化式の解が正しいことの証明
*)
  Lemma r_rel_sol n : R_rel n = R_sol n.
  Proof.
    elim: n => [| n IHn].
    - rewrite /R_rel /R_sol /=.
      by ssromega.
    - rewrite R_rel_n IHn /R_sol.
      by apply: alpha_beta_gamma.           (* 共通の数式の証明 *)
  Qed.
  
(**
総和の式と漸化式の解が等しいことの証明
*)
  Lemma r_sum_sol (n : nat) : R_sum n = R_sol n.
  Proof.
    elim: n => [| n IHn].
    - rewrite /R_sum /R_sol.
      (* 右辺 *)
      rewrite exp0n // addnn double0 -divn2 div0n 2!mul0n 2!addn0.
      (* 左辺 *)
      rewrite big_nil add0n.
      done.
    - rewrite /R_sum /R_sol.
      rewrite /R_sum /R_sol in IHn.
      rewrite sum_last //.

      (* 左辺 *)
      rewrite -addnA [beta + gamma * n.+1 + alpha]addnC addnA.
      rewrite IHn.
      rewrite addnA.
      by apply: alpha_beta_gamma.           (* 共通の数式の証明 *)
  Qed.
  
(**
総和の式と漸化式が等しいことの証明
*)
  Lemma r_sum_rel (n : nat) : R_sum n = R_rel n.
  Proof.
    elim: n => [| n IHn].
    - rewrite /R_sum /R_rel.
      rewrite big_nil.
      done.

    - rewrite /R_sum R_rel_n.
      rewrite /R_sum in IHn.
      
      (* 左辺 *)
      rewrite sum_last //.
      rewrite -addnA [beta + gamma * n.+1 + alpha]addnC addnA.
      rewrite IHn.
      rewrite addnA.
      
      by congr (_ + _).
  Qed.
  
End Recrel.

Section Example1.

  Variable a b : nat.
(**
左辺が 0 始まりであることに注意。
*)
  Example ex1 (n : nat) :
    \sum_(0 <= i < n.+1) (a + b * i) = n.+1 * a + (n^2 + n)./2 * b.
  Proof.
(**
   alpha := a
   beta := a
   gamma := b
*)
    move: (r_sum_sol a a b).
    rewrite /R_sum /R_sol => <-.
    rewrite sum_first => //.
    by ssromega.
  Qed.
  
End Example1.

(**
# 参考文献

Knuth 他著、有沢他訳、「コンピュータの数学」 共立出版。第２章
*)

(* END *)
