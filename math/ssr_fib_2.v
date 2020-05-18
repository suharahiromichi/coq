(**
フィボナッチ数列についての定理の証明

フィボナッチ数列と中学入試問題
http://www.suguru.jp/Fibonacci/
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import ssr_fib_1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
ffibonacci
 *)

Section Fib_2.

  Print fib.                                (* ****** *)
  
  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

  Lemma fib_1_le_fib2 n : 1 <= fib n.+2.
  Proof.
    elim: n => // n IHn.
    rewrite fib_n.
    rewrite addn_gt0.
      by apply/orP/or_intror.
  Qed.

(**
## 性質1（フィボナッチ数列の和）

```Ｆ1 ＋ Ｆ2 ＋ … ＋ Ｆn ＝ Ｆn+2 － 1```

ここでは、帰納法で解く。
 *)
  Lemma lemma1' (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = fib n.+2 - 1.
  Proof.  
    elim: n => [| n IHn].
    - rewrite big_cons big_nil /=.
        by ssromega.
    - rewrite l_last; last done.            (* ****** *)
      rewrite IHn.
      rewrite addnBAC; last by rewrite fib_1_le_fib2.
      congr (_ - _).
        by rewrite addnC.
  Qed.

(**
## 性質2（積の和）

```Ｆ1 × Ｆ1 ＋ Ｆ2 × Ｆ2 ＋ … ＋ Ｆn × Ｆn ＝ Ｆn × Ｆn+1```
*)
  Lemma lemma2 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i * fib i) = fib n * fib n.+1.
  Proof.
    elim: n.
    - by rewrite big_cons big_nil /=.
    - move=> n IHn.
      rewrite l_last; last done.
      rewrite IHn.
      rewrite -mulnDl.
      rewrite mulnC.
        by congr (_ * _).
  Qed.

(**
## 性質3 (奇数の和）

```Ｆ1 ＋ Ｆ3 ＋ Ｆ5 ＋ … ＋ Ｆ2n-1 ＝ Ｆ2n```
*)  
  Lemma lemma3 (n : nat) :
    \sum_(0 <= i < n)(fib i.*2.+1) = fib n.*2.
  Proof.
    elim: n.
    - by rewrite big_nil.
    - move=> n IHn.
      have -> : n.+1.*2 = n.*2.+2.
      + rewrite -addn1 -!muln2.
          by ssromega.
      + rewrite fib_n.                      (* 右辺 *)
        rewrite l_last; last done.          (* 左辺 *)
        rewrite IHn.
          by congr (_ + _).
  Qed.

(**
## 性質4（偶数の和）

```Ｆ2 ＋ Ｆ4 ＋ Ｆ6 ＋ … ＋ Ｆ2n ＋ １ ＝ Ｆ2n+1```
*)
  Lemma lemma4 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i.*2) + 1 = fib n.*2.+1.
  Proof.
    elim: n.
    - by rewrite big_cons big_nil /=.
    - move=> n IHn.
      have H : n.+1.*2 = n.*2.+2
        by rewrite -addn1 -!muln2 addn1 2!muln2 doubleS.
      (* 右辺 *)
      rewrite H.
      rewrite !fib_n.
      rewrite -{1}IHn.
      rewrite -addnA.
      rewrite -fib_n.
      rewrite [1 + fib n.*2.+2]addnC.
      
      (* 左辺 *)      
      rewrite l_last; last done.
      rewrite -H -addnA.
      done.
  Qed.

(**
## 性質5（となり同士のフィボナッチ数列は互いに素である。）
 *)
  Lemma lemma5 (n : nat) : coprime (fib n) (fib n.+1).
  Proof.
    rewrite /coprime.
    elim: n => [//= | n IHn].
    rewrite fib_n.
      by rewrite gcdnDr gcdnC.
  Qed.

(**
## 性質6（Ｆn+m ＝ Ｆm × Ｆn+1 ＋ Ｆm-1 × Ｆn）

フィボナッチ数列の加法定理
 *)
  Axiom nat_fib_ind : forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P n.+1 -> P n.+2) ->
      forall n : nat, P n.
  
  Lemma fib_addition' n m :
    fib (n + m.+1) = fib m.+1 * fib n.+1 + fib m * fib n.
  Proof.
    elim/nat_fib_ind : m.
    - rewrite addn1.
      rewrite [fib 1]/= mul1n.
      rewrite [fib 0]/= mul0n !addn0.
      done.
      
    - rewrite addn2.
      rewrite [fib 2]/= add0n mul1n.
      rewrite [fib 1]/= mul1n.
      rewrite fib_n.
      rewrite addnC.
      done.

    - move=> m IHm IHm1.
      rewrite fib_n mulnDl.
      rewrite {2}fib_n mulnDl.
      
      (* F(n + m.+1) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fib m * fib n]addnC. (* この項を先頭に。 *)
      rewrite ?addnA [_ + fib m.+1 * fib n.+1]addnC ?addnA. (* この項を先頭に。 *)
      rewrite -IHm.
       
      (* F(n + m.+2) の項をまとめて置き換える *)
      rewrite ?addnA [_ + fib m.+1 * fib n]addnC. (* この項を先頭に。 *)
      rewrite ?addnA [_ + fib m.+2 * fib n.+1]addnC ?addnA. (* この項を先頭に。 *)
      rewrite -IHm1.
      
      have -> : n + m.+3 = (m + n).+3 by ssromega.
      have -> : n + m.+2 = (m + n).+2 by ssromega.
      have -> : n + m.+1 = (m + n).+1 by ssromega.
      rewrite fib_n.
      rewrite [fib (m + n).+2 + fib (m + n).+1]addnC.
      done.
  Qed.
  
  Lemma fib_addition n m :
    1 <= m -> fib (n + m) = fib m * fib n.+1 + fib m.-1 * fib n.
  Proof.
    move=> H.
    have H' := fib_addition' n m.-1.
      by rewrite prednK in H'.
  Qed.

(**
## 性質7（nがmで割り切れるならば，ＦnはＦmで割り切れる。）

n = qm ならば，ＦnはＦmで割り切れる。
*)
  Lemma lemma7' (m q : nat) : fib m.+1 %| fib (q.+1 * m.+1).
  Proof.
    elim: q => [| q IHq].
    - by rewrite mulSn mul0n addn0.
    - rewrite [q.+2 * m.+1]mulSn.
      rewrite addnC.
      rewrite fib_addition'.
      apply: dvdn_add.
      + by apply: dvdn_mulr.
      + by apply: dvdn_mull.
  Qed.
  
  Lemma lemma7 (m q : nat) : 1 <= m -> 1 <= q -> fib m %| fib (q * m).
  Proof.
    move=> Hm Hq.
    have H' := lemma7' m.-1 q.-1.
    rewrite prednK in H' ; last done.
    rewrite prednK in H' ; last ssromega.
    done.
  Qed.

(**
## 性質8（ＦmとＦm+nの最大公約数 ＝ ＦmとＦnの最大公約数）

```gcd (F m) (F m+n) = gcd (F m) (F n)```
*)
  Lemma lemma8' (m n : nat) :
    gcdn (fib m) (fib (m + n.+1)) = gcdn (fib m) (fib n.+1).
  Proof.
    rewrite fib_addition'.
    rewrite addnC gcdnMDl.
    rewrite Gauss_gcdl; last by rewrite lemma5.
    done.
  Qed.

  Lemma lemma8 (m n : nat) :
    1 <= n -> gcdn (fib m) (fib (m + n)) = gcdn (fib m) (fib n).
  Proof.
    move=> H.
    rewrite fib_addition; last done.
    rewrite addnC gcdnMDl.
    rewrite Gauss_gcdl; last by rewrite lemma5.
    done.
  Qed.

(**
## 補題9_1（m を n で割ったときのあまりを r とすると，
ＦmとＦnの最大公約数 ＝ ＦnとＦrの最大公約数）
 *)
  Lemma lemma91' (n q r : nat) :
    gcdn (fib (q.+1 * n.+1 + r.+1)) (fib n.+1) = gcdn (fib n.+1) (fib r.+1).
  Proof.
    elim: q => [| q IHq].
    - rewrite mul1n gcdnC.
      rewrite lemma8'.
      done.
    - rewrite gcdnC mulSn addnC -?addnA addnCA.
      rewrite lemma8.
      + by rewrite gcdnC addnC.
      + by rewrite addnC addnS ltn0Sn.
  Qed.
  
  Lemma lemma91'' (n q r : nat) :
    gcdn (fib (q.+1 * n + r.+1)) (fib n) = gcdn (fib n) (fib r.+1).
  Proof.
    elim: q => [| q IHq].
    - by rewrite mul1n gcdnC lemma8'.
    - rewrite gcdnC mulSn addnC -?addnA addnCA.
      rewrite lemma8.
      + by rewrite gcdnC addnC.
      + by rewrite addnC addnS ltn0Sn.
  Qed.
  
  Lemma lemma91''' (n q r : nat) :
    gcdn (fib (q * n + r.+1)) (fib n) = gcdn (fib n) (fib r.+1).
  Proof.
    elim: q => [| q IHq].
    - by rewrite gcdnC mul0n add0n.
    - rewrite gcdnC mulSn addnC -?addnA addnCA.
      rewrite lemma8.
      + by rewrite gcdnC addnC.
      + by rewrite addnC addnS ltn0Sn.
  Qed.

  Lemma lemma91_r1 (n q r : nat) :
    1 <= r ->
    gcdn (fib (q * n + r)) (fib n) = gcdn (fib n) (fib r).
  Proof.
    move=> H.
    have H' := lemma91''' n q r.-1.
      by rewrite prednK in H'.
  Qed.

  Lemma gcdn0 (n : nat) : gcdn n 0 = n.
  Proof.
    by elim: n.
  Qed.
  
  (* r = 0 の特別な場合は、性質7である。 *)
  Lemma lemma91_r0 (n q : nat) :
    1 <= n ->
    1 <= q ->
    gcdn (fib (q * n)) (fib n) = gcdn (fib n) (fib 0).
  Proof.
    move=> Hn Hq.
    rewrite [fib 0]/= gcdn0.
    apply/gcdn_idPr.
      by apply/lemma7.
  Qed.

  Lemma lemma91 (n q r : nat) :
    1 <= n ->
    1 <= q ->
    gcdn (fib (q * n + r)) (fib n) = gcdn (fib n) (fib r).
  Proof.  
    move=> Hn Hq.
    case Hr : (r == 0).
    - move/eqP in Hr.
      rewrite Hr addn0.
        by apply: lemma91_r0.
    - move/eqP in Hr.
      move/PeanoNat.Nat.neq_0_lt_0 in Hr.
      move/ltP in Hr.
      by rewrite lemma91_r1.
  Qed.
  
(**
## 性質9（ＦmとＦnの最大公約数 ＝ Ｆ(mとnの最大公約数)）

```gcd (F m) (F n) = F (gcd m n)```
*)
  Lemma gcdn (m n : nat) : gcdn (fib m) (fib n) = fib (gcdn m n).
  Proof.
  Admitted.

End Fib_2.
  
(* END *)
