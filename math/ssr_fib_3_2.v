(**
フィボナッチ数の最大公約数 (GCD of Fibonacci Numbers)
============================

@suharahiromichi

2022/01/29
*)

(**
このソースは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_fib_3_2.v
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Fib3_2.

(**  
# フィボナッチ数の定義と定理
*)
  Fixpoint fibn (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fibn m + fibn pn (* fibn n.-2 + fibn n.-1 *)
    end.
  
(**
1個分のフィボナッチ数の計算
 *)
  Lemma fibn_n n : fibn n.+2 = fibn n + fibn n.+1.
  Proof.
    done.
  Qed.

(**
隣り合ったフィボナッチ数は互いに素である。
*)
  Lemma fibn_coprime (n : nat) : coprime (fibn n) (fibn n.+1).
  Proof.
    rewrite /coprime.
    elim: n => [//= | n IHn].
    rewrite fibn_n.
      by rewrite gcdnDr gcdnC.
  Qed.
  
(**
フィボナッチ数列の加法定理
*)
  Lemma fibn_addition n m :
    1 <= m -> fibn (n + m) = fibn m * fibn n.+1 + fibn m.-1 * fibn n.
  Proof.
    (* see. ssr_fibn_2.v
       これも functional induction を使わずに証明したい。 *)
  Admitted.                                 (* OK *)

(**
# フィボナッチ数のGCD
*)

(**
GKPの解答にある、``m > n`` ならば ``gcd (fibn m) (fibn n) = gcd (fibn (m - n)) (fibn n)``
と同じものを証明するが、そのために ``m`` を ``0`` と非0で振り分ける。
 *)
  Lemma fibn_lemma_gkp' m n :
    1 <= m -> gcdn (fibn (n + m)) (fibn n) = gcdn (fibn m) (fibn n).
  Proof.
    move=> H.
    rewrite fibn_addition //.
    rewrite gcdnC addnC gcdnMDl.
    rewrite Gauss_gcdl.
    - by rewrite gcdnC.
    - by apply: fibn_coprime.
  Qed.
  
  Lemma fibn_lemma_gkp m n :
    gcdn (fibn (n + m)) (fibn n) = gcdn (fibn m) (fibn n).
  Proof.
    case: m => [| m].
    - rewrite addn0 /=.
        by rewrite gcd0n gcdnn.
    - by rewrite fibn_lemma_gkp'.
  Qed.
  
(**
gcdnMDl のフィボナッチ数版
*)
  Check gcdnMDl : forall k m n : nat, gcdn m (k * m + n) = gcdn m n.
  Lemma fibn_gcdMDl n q r :
    gcdn (fibn (q * n + r)) (fibn n) = gcdn (fibn n) (fibn r).
  Proof.
    elim: q => [| q IHq].
    - rewrite mul0n add0n.
      rewrite gcdnC.
      done.
    - Search _ (_.+1 * _).
      rewrite mulSn -addnA.
      rewrite [LHS]fibn_lemma_gkp.
      done.
  Qed.
  
(**
gcdn_modr のフィボナッチ数版
*)
  Check gcdn_modr : forall m n : nat, gcdn m (n %% m) = gcdn m n.
  Lemma fibn_gcdn_modr m n :
    gcdn (fibn m) (fibn n) = gcdn (fibn n) (fibn (m %% n)).
  Proof.
    move: (fibn_gcdMDl n (m %/ n) (m %% n)).
    rewrite -divn_eq.
    done.
  Qed.

(**
# GCDの帰納法の証明

Coq Tokyo 終了後に教えてもらった GCD の帰納法です。
*)
  Lemma my_gcdn_ind (P : nat -> nat -> nat -> Prop) :
    (forall n, P 0 n n) ->
    (forall m n, P (n %% m) m (gcdn (n %% m) m) -> P m n (gcdn m n)) ->
    forall m n, P m n (gcdn m n).
(*  Proof.
    move => H0 Hmod.
    elim /ltn_ind => [[| m ]] // H n.
    apply : Hmod. exact : H (ltn_mod _ _) _.
  Qed.
*)
  Admitted.
  
(**
functional induction を使わずに証明します。
*)
  Theorem gcdn_fibn__fibn_gcdn (m n : nat) : gcdn (fibn m) (fibn n) = fibn (gcdn m n).
  Proof.
    Check @my_gcdn_ind (fun m0 n0 n1 => (gcdn (fibn m0) (fibn n0) = fibn n1)).
    apply: (@my_gcdn_ind (fun m0 n0 n1 => (gcdn (fibn m0) (fibn n0) = fibn n1))).
    - move=> n'.
        by rewrite /= gcd0n.
    - move=> m' n' /= IHm.
      rewrite gcdnC -fibn_gcdn_modr gcdn_modl gcdnC in IHm.
      rewrite IHm gcdnC.
      done.
  Qed.

End Fib31.
