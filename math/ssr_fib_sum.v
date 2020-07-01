(**
フィボナッチ数列の和
========================

@suharahiromichi

2020/07/01
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

フィボナッチ ffibonacci 数列の和はいくつかのおもしろい性質があります。
どれも、中学生の数学で証明できるものですが、
ここでは、``Σ``の定義と関連する
補題を含む MathComp の big.v ライブラリを使って証明してみましょう。

 *)

Section Fib_1.

(**
# fibonacci 関数の定義
*)
  Fixpoint fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
 
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
### 最後の1項を取り出す。

```Σ(i=m..n)f(i) = Σ(i=m..n-1)f(i) + f(n)```

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_doc.pdf

ただし、f(n)が前に出ていて、見落としてしまう。つぎの p.136 も見よ。

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/ssrcoq.pdf
 *)
  Lemma l_last m n f :
    m <= n ->
    \sum_(m <= i < n.+1)(f i) = \sum_(m <= i < n)(f i) + f n.
  Proof.
    move=> Hmn.
      by rewrite big_nat_recr.
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
    - rewrite l_last; last done.
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

 
End Fib_1.

(* END *)
