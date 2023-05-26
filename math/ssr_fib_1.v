(**
フィボナッチ数列についての定理の証明

フィボナッチ数列と中学入試問題
http://www.suguru.jp/Fibonacci/
*)

From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
ffibonacci
 *)

Section Fib_1.

(**
# fibonacci 関数の定義
*)
  Fixpoint fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (ppn.+1 as pn).+1 => fib ppn + fib pn (* fib n.-2 + fib n.-1 *)
    end.

(**
## 定理 性質1

```Σ(i=0..n)fib(i) = fib n+2 - 1```
 *)

(**
### fib数列の和の加算

```Σf + Σg = Σ(f + g)```

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_doc.pdf
*)
  Lemma l_sum_of_seq (n : nat) :
    \sum_(0 <= i < n)(fib i) + \sum_(0 <= i < n)(fib i.+1) =
    \sum_(0 <= i < n)(fib i.+2).
  Proof.
    rewrite -big_split.
    done.
  Qed.
  
(**
### index を 0起源に振りなおす。

```Σ(i=m..n+m)f(i) = Σ(i=0..n)f(i+m)```
 *)
  Lemma l_reindex (m n : nat) :             (* 不使用 *)
    \sum_(m <= i < n + m)(fib i) = \sum_(0 <= i < n)(fib (i + m)).
  Proof.
    rewrite -{1}[m]add0n.
    rewrite big_addn.
    have -> : n + m - m = n by ssromega.
    done.
  Qed.
  
  Lemma l_reindex_1 (n : nat) :
    \sum_(1 <= i < n.+1)(fib i) = \sum_(0 <= i < n)(fib i.+1).
  Proof.
      by rewrite big_add1 succnK.
  Qed.
  
  Lemma l_reindex_2 (n : nat) :
    \sum_(2 <= i < n.+2)(fib i) = \sum_(0 <= i < n)(fib i.+2).
  Proof.
      by rewrite 2!big_add1 2!succnK.
  Qed.
  

(**
### 最初の1項を取り出す。

```Σ(i=m..n)f(i) = f(m) + Σ(i=m+1..n)f(i)```
 *)
  Lemma l_first m n f :
    m < n ->
    \sum_(m <= i < n)(f i) = f m + \sum_(m.+1 <= i < n)(f i).
  Proof.
    move=> Hn.
      by rewrite big_ltn.
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
## コンギュランス
*)
  Lemma eq_add m n k : (m + k = n + k) <-> (m = n).
  Proof.
    split=> H.
    - apply/eqP.
      rewrite -(eqn_add2r k).
        by apply/eqP.
    - by rewrite H.
  Qed.

(**
### 定理

```Σ(i=0..n)fib(i) = fib n+2 - 1```
*)
  Lemma lemma1 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = fib n.+2 - 1.
  Proof.  
    have H := l_sum_of_seq n.+1.
    rewrite -l_reindex_1 -l_reindex_2 in H.
    rewrite [\sum_(1 <= i < n.+2)(fib i)]l_first in H; last done.
    rewrite [\sum_(2 <= i < n.+3)(fib i)]l_last in H; last done.
    rewrite addnA in H.
    rewrite [\sum_(2 <= i < n.+2) fib i + fib n.+2]addnC in H.
    move/eq_add in H.
    rewrite -H.
    rewrite [fib 1]/=.
      by rewrite addn1 subn1 succnK.
  Qed.

End Fib_1.

(* 使わなかった補題 *)

Section Backup.

  Lemma fib_0 n : fib 0 * fib n = 0.
  Proof.
      by rewrite mul0n.
  Qed.
  
  Lemma fib_1 n : fib 1 * fib n = fib n.
  Proof.
      by rewrite mul1n.
  Qed.
        
  Lemma fib_2 n : fib 2 * fib n = fib n.
  Proof.
      by rewrite mul1n.
  Qed.

  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

  Lemma l1_sub2 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = \sum_(0 <= i < n)(fib i.+1).
  Proof.
    have H : 0 <= n by rewrite leq0n.
    Check (big_nat_recl n 0 _ H).
    rewrite big_nat_recl; last done.
      by rewrite add0n.
  Qed.
  
  Lemma l1_sub3 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i.+1) = 1 + \sum_(0 <= i < n)(fib i.+2).
  Proof.
    have H : 0 <= n.+1 by rewrite leq0n.
    Check (big_nat_recl n 0 _ H).
    rewrite big_nat_recl; last done.
      by rewrite [fib 1]/=.
  Qed.
  
  Lemma test1 : fib 1 = \sum_(0 <= i < 1)(fib i.+1).
  Proof.
    rewrite big_cons.
    rewrite big_nil.
    done.
  Qed.
  
  Lemma l1_sub2' (n : nat) :
    1 <= n -> \sum_(1 <= i < n.+1)(fib i) = fib 1 + \sum_(1 <= i < n)(fib i.+1).
  Proof.
    move=> H.
    rewrite -big_nat_recl; last done.
    done.
  Qed.

  Lemma test2 : fib 1 = \sum_(0 <= i < 1)(fib i.+1).
  Proof.
      by rewrite big_cons big_nil.
  Qed.
  
  Lemma test0 : \sum_(0 <= i < 1)(fib i) = 0.
  Proof.
      by rewrite big_cons big_nil.
  Qed.
  
  Lemma cat_iota (n : nat) : 1 <= n -> index_iota 0 1 ++ index_iota 1 n = index_iota 0 n.
  Proof.
    move=> Hn.
    rewrite /index_iota.
    rewrite -iotaD.
    rewrite !subn0.
    rewrite subnKC //=.
  Qed.

  Lemma test4 (n : nat) :
    1 <= n ->
    \sum_(0 <= i < 1)(fib i) + \sum_(1 <= i < n)(fib i) =
    \sum_(0 <= i < n)(fib i).
  Proof.
    move=> Hn.
    rewrite -big_cat.
    rewrite cat_iota; last done.
    done.
    
    (* l_first を使えばよい。 *)
    Restart.
    move=> Hn.
    rewrite [\sum_(0 <= i < n) fib i]l_first; last done.
    by rewrite big_cons big_nil.
  Qed.

End Backup.

(* END *)
