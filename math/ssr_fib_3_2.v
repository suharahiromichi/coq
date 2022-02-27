(**
フィボナッチ数の最大公約数 (GCD of Fibonacci Numbers)
============================

@suharahiromichi

2022/01/29

2022/02/27 fibn_ind と gcdn_ind を証明して、
functional inducntion　を使わずに証明した。
*)

(**
# はじめに

フィボナッチ数の最大公約数は、その最大公約数番目のフィボナッチ数に等しい、

```math

gcd(F_m, F_n) = F_{gcd(m, n)}
```

という定理があります。エドゥアール・リュカ（François Édouard Anatole Lucas) が発見して、
クヌーツ先生の本 [1] (式 6.111) で有名になったのだそうです。

フィボナッチ数の加法定理 [2] をつかうと簡単に証明できるので、トライしてみましょう。


このソースは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_fib_3_2.v
*)

From mathcomp Require Import all_ssreflect.
(* From common Require Import ssromega. *)

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
## 簡単な補題
*)

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
## フィボナッチ数列の帰納法
*)
  Definition Pfibn m0 n0 :=
    forall n, fibn (n + m0.+1) = fibn m0.+1 * fibn n.+1 + n0 * fibn n.

  Lemma fibn_ind (P : nat -> nat -> Prop) :
    P 0 0 ->
    P 1 1 ->
    (forall m : nat, P m (fibn m) ->
                     P m.+1 (fibn m.+1) ->
                     P m.+2 (fibn m + fibn m.+1))
    ->
      forall m : nat, P m (fibn m).
  Proof.
    move=> H1 H2 IH.
    (* m について2回場合分して、m.+2 を取り出す。 *)
    elim/ltn_ind => [[_ | [_ | m]]].
    - by rewrite /fibn.
    - by rewrite /fibn.
    - move: (IH m).
      rewrite -fibn_n => {IH} IH H.
      by apply: IH; apply: H.
  Qed.
  
  Check @fibn_ind Pfibn
    : Pfibn 0 0 ->
      Pfibn 1 1 ->
      (forall m : nat, Pfibn m (fibn m) ->
                       Pfibn m.+1 (fibn m.+1) ->
                       Pfibn m.+2 (fibn m + fibn m.+1))
      ->
        forall m : nat, Pfibn m (fibn m).
  
(**
## フィボナッチ数列の加法定理

fibn_ind を使って、functional induction を使わずに証明します。
*)
  Lemma fibn_addition' m n :
    fibn (m + n.+1) = fibn n.+1 * fibn m.+1 + fibn n * fibn m.
  Proof.
    apply: (@fibn_ind Pfibn); rewrite /Pfibn.
    - clear m n => n.
      rewrite addn1.
      rewrite [fibn 1]/= mul1n mul0n addn0.
      done.
      
    - clear m n => n.
      rewrite addn2.
      rewrite [fibn 2]/= add0n 2!mul1n.
      rewrite addnC -fibn_n.
      done.
      
    - clear m n => m IHn0 IHn1 n.
      rewrite fibn_n 2!mulnDl.
      
      (* F(n + m.+1) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fibn m * fibn n]addnC. (* この項を先頭に。 *)
      rewrite ?addnA [_ + fibn m.+1 * fibn n.+1]addnC ?addnA. (* この項を先頭に。 *)
      rewrite -IHn0.
       
      (* F(n + m.+2) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fibn m.+1 * fibn n]addnC. (* この項を先頭に。 *)
      rewrite ?addnA [_ + fibn m.+2 * fibn n.+1]addnC ?addnA. (* この項を先頭に。 *)
      rewrite -IHn1.

      rewrite -addn3 addnA addn3.
      rewrite -[m.+2]addn2 addnA addn2.
      rewrite -[m.+1]addn1 addnA addn1.
      rewrite fibn_n addnC.
      done.
  Qed.
  
  Lemma fibn_addition m n :
    1 <= n -> fibn (m + n) = fibn n * fibn m.+1 + fibn n.-1 * fibn m.
  Proof.
    move=> H.
    have H' := fibn_addition' m n.-1.
    by rewrite prednK in H'.
  Qed.

(**
# GCDの帰納法の証明

Coq Tokyo 終了後に教えてもらった GCD の帰納法です。
*)
  Definition Pgcdn m0 n0 n1 := gcdn (fibn m0) (fibn n0) = fibn n1.
  
  Lemma gcdn_ind (P : nat -> nat -> nat -> Prop) :
    (forall n, P 0 n n) ->
    (forall m n, P (n %% m) m (gcdn (n %% m) m) ->
                 P m n (gcdn m n))
    ->
      forall m n, P m n (gcdn m n).
  Proof.
    move => H0 Hmod.
    elim/ltn_ind => [[| m]] // H n.
    - have -> : gcdn 0 n = n by elim: n.
      done.
    - apply : Hmod.
      exact : H (ltn_mod _ _) _.
  Qed.

  Check @gcdn_ind Pgcdn
    : (forall n : nat, Pgcdn 0 n n) ->
      (forall m n : nat, Pgcdn (n %% m) m (gcdn (n %% m) m) -> Pgcdn m n (gcdn m n)) ->
      forall m n : nat, Pgcdn m n (gcdn m n).

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
gcdn_ind を使って、functional induction を使わずに証明します。
*)
  Theorem gcdn_fibn__fibn_gcdn (m n : nat) : gcdn (fibn m) (fibn n) = fibn (gcdn m n).
  Proof.
    apply: (@gcdn_ind Pgcdn); rewrite /Pgcdn.
    - move=> n'.
      by rewrite /= gcd0n.
    - move=> m' n' /= IHm.
      rewrite gcdnC -fibn_gcdn_modr gcdn_modl gcdnC in IHm.
      by rewrite IHm gcdnC.
  Qed.
  
End Fib3_2.

(**
# 文献

[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition


[2] https://github.com/suharahiromichi/coq/blob/master/math/ssr_fib_2.v
 *)

(* END *)
