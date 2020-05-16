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
  

End Fib_2.
  
(* END *)
