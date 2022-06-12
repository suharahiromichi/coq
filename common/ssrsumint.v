(**
総和（Σ）の補題 整数版

2020_8_22 @suharahiromichi 自然数
2022_6_12 @suharahiromichi 整数
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From common Require Import ssromega. (* ssromega *)

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Summation1.
(**
## 総和の結合と分配

高校で習う、総和についての公式です。

総和の範囲は、$m \lt n$ としてmからnとします。
$m \ge n$ の場合は、Σの中身が単位元となり成立しません。

```math

\sum_{i=m}^{n-1}a_i + \sum_{i=m}^{n-1}b_i = \sum_{i=m}^{n-1}(a_i + b_i) \\

\sum_{i=m}^{n-1}c a_i = c \sum_{i=m}^{n-1}a_i \\

\sum_{i=m}^{n-1}(a_i c) = (\sum_{i=m}^{n-1}a_i) c \\

\sum_{i=m}^{n-1} c = (n - m) c \\

```
*)
  Lemma sum_split (m n : nat) (a b : nat -> int) :
    (m < n)%N ->
    \sum_(m <= i < n)(a i) + \sum_(m <= i < n)(b i) = \sum_(m <= i < n)(a i + b i).
  Proof. by rewrite big_split. Qed.
  
  Lemma sum_distrr (m n : nat) (c : int) (a : nat -> int) :
    (m < n)%N ->
    \sum_(m <= i < n)(c * (a i)) = c * (\sum_(m <= i < n)(a i)).
  Proof. by rewrite big_distrr. Qed.
  
  Lemma sum_distrl (m n : nat) (a : nat -> int) (c : nat) :
    (m < n)%N ->
    \sum_(m <= i < n)((a i) * c) = (\sum_(m <= i < n)(a i)) * c.
  Proof. by rewrite big_distrl. Qed.
  
  Lemma sum_nat_const_int (m n : nat) (c : int) :
    (m < n)%N ->
    \sum_(m <= i < n) c = (n - m)%:Z * c.
  Proof.
    move=> H.
    rewrite big_const_nat.
    rewrite iter_addr_0.
    rewrite mulrC.
    rewrite -mulr_natr natz.
    done.
  Qed.
  
(**
# Σの中身の書き換え

Σの中の i は、ローカルに束縛されている（ラムダ変数である）ので、
直接書き換えることはできません。一旦、取り出して書き換えることになります。
 *)
  Lemma eq_sum (m n : nat) (a b : nat -> int) : a =1 b ->
                         \sum_(m <= i < n)(a i) = \sum_(m <= j < n)(b j).
  Proof.
    move=> Hab.                             (* =1 は第1階の=です。 *)
    apply: eq_big_nat => i Hmn.
      by rewrite Hab.
  Qed.
  
(**
# 入れ子（ネスト）
 *)
(**
## ネストの入れ替え（総和どうしの場合）

$$ \sum_{i=0}^{m-1}(\sum_{j=0}^{n-1)} a_{i j} =
   \sum_{j=0}^{n-1}(\sum_{i=0}^{m-1)} a_{i j} $$
*)
  Lemma exchamge_sum (m n : nat) (a : nat -> nat -> int) :
    \sum_(0 <= i < m) (\sum_(0 <= j < n) (a i j)) =
    \sum_(0 <= j < n) (\sum_(0 <= i < m) (a i j)).
  Proof. by rewrite exchange_big. Qed.
  
(**
# Σを消す
 *)
(**
## 0を取り出す。

$$ \sum_{i \in \emptyset}a_i = 0 $$

総和をとる範囲が無い場合（0以上0未満）は、単位元``0``になります。
 *)
  Lemma sum_nil' (a : nat -> int) : \sum_(0 <= i < 0)(a i) = 0.
  Proof.
    by rewrite big_nil.
  Qed.
  
(**
上記の補題は、1以上1未満などの場合にも適用できてしまいますが、任意のmとnで証明しておきます。
*)
  Lemma sum_nil (m n : nat) (a : nat -> int) :
    (n <= m)%N -> \sum_(m <= i < n)(a i) = 0.
  Proof.
    move=> Hmn.
    have H : \sum_(m <= i < n)(a i) = \sum_(i <- [::])(a i).
    - apply: congr_big => //=.
      rewrite /index_iota.
      have -> : (n - m = 0)%N by ssromega. (* apply/eqP; rewrite subn_eq0. *)
      done.
    - rewrite H.
      by rewrite big_nil.
  Qed.

(**
## ``a_n``項を取り出す。

$$ \sum_{i=n}^{n}a_i = a_n $$

総和をとる範囲がひとつの項の場合（n以上n以下）は、``a n`` となります。
 *)
  Lemma sum_nat1 (n : nat) (a : nat -> int) :
    \sum_(n <= i < n.+1)(a i) = a n.
  Proof. by rewrite big_nat1. Qed.

(**
# インデックスを調整する補題
*)
(**
## 総和の範囲を0起源に振りなおす。

項のインデックスを調整して（ずらして）、mからn+mまでの総和の範囲を0からnまでにします。

$$ \sum_{i=m}^{n+m-1}a_i = \sum_{i=0}^{n-1}a_{i+m} $$
 *)
  Lemma sum_addn (m n : nat) (a : nat -> int) :
    \sum_(m <= i < n + m)(a i) = \sum_(0 <= i < n)(a (i + m)%N).
  Proof.
    rewrite -{1}[m]add0n.
    rewrite big_addn.
    have -> : (n + m - m = n)%N by ssromega.
    done.
  Qed.

(**
これは、任意のmで成り立ちますが、``Σ``の中の項のインデックスの``i.+1``を
``i + 1`` に書き換えられないため、``i.+1`` と ``i.+2`` の場合については、
個別に用意する必要があります。実際はこちらの方を使います。
*)
  Lemma sum_add1 (n : nat) (a : nat -> int) :
    \sum_(1 <= i < n.+1)(a i) = \sum_(0 <= i < n)(a i.+1).
  Proof. by rewrite big_add1 succnK. Qed.
  
  Lemma sum_add2 (n : nat) (a : nat -> int) :
    \sum_(2 <= i < n.+2)(a i) = \sum_(0 <= i < n)(a i.+2).
  Proof. by rewrite 2!big_add1 2!succnK. Qed.
  
(**
# 最初の項、または、最後の項をΣの外に出す。
 *)
(**
## 最初の項をΣの外に出す。

$$ \sum_{i=m}^{n-1}a_i = a_m + \sum_{i=m+1}^{n-1}a_i $$
 *)
  Lemma sum_first (m n : nat) (a : nat -> int) :
    (m < n)%N ->
    \sum_(m <= i < n)(a i) = a m + \sum_(m.+1 <= i < n)(a i).
  Proof.
    move=> Hn.
    by rewrite big_ltn.
  Qed.

(**
総和の範囲の起点を変えずに、インデックスをずらす補題もあります。

$$ \sum_{i=m}^{n}a_i = a_m + \sum_{i=m}^{n-1}a_{i + 1} $$
*)
  Lemma sum_first' (m n : nat) (a : nat -> int) :
    (m <= n)%N ->
    \sum_(m <= i < n.+1)(a i) = a m + \sum_(m <= i < n)(a i.+1).
  Proof.
    move=> Hn.
    by rewrite big_nat_recl.
  Qed.
  
(**
## 最後の項をΣの外に出す。

n(インデックスの上限)についての帰納法と組み合わせて使います。

$$ \sum_{i=m}^{n}a_i = \sum_{i=m}^{n-1}a_i + a_n $$
 *)
  Lemma sum_last (m n : nat) (a : nat -> int) :
    (m <= n)%N ->
    \sum_(m <= i < n.+1)(a i) = \sum_(m <= i < n)(a i) + a n.
  Proof.
    move=> Hmn.
    by rewrite big_nat_recr.
  Qed.

(**
## 数列の分割と結合

$$ \sum_{i=m}^{p}a_i = \sum_{i=m}^{n}a_i + \sum_{i=n}^{p}a_i $$
 *)
  Lemma sum_cat' (m n1 n2 n : nat) (a : nat -> int) :
    \sum_(m <= i < m + n1 + n2) a i =
    \sum_(m <= i < m + n1) a i + \sum_(m + n1 <= i < m + n1 + n2) a i.
  Proof.
    rewrite -big_cat.
    f_equal.                       (* iインデックス部分を取り出す。 *)
    rewrite /index_iota.
    Check iota_add
      : forall m n1 n2 : nat, iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
    have -> : (m + n1 + n2 - m = n1 + n2)%N by ssromega.
    have -> : (m + n1 - m = n1)%N by ssromega.
    have -> : (m + n1 + n2 - (m + n1) = n2)%N by ssromega.
    rewrite -iota_add.
    done.
  Qed.
  
  (* big_cat_nat を使えば、直接証明できる。 *)
  Lemma sum_cat (m n p : nat) (a : nat -> int) :
    (m <= n)%N -> (n <= p)%N ->
    \sum_(m <= i < p) a i = \sum_(m <= i < n) a i + \sum_(n <= i < p) a i.
  Proof.
    move=> Hmn Hnp.
    by rewrite -big_cat_nat.
      
    Restart.
    move=> Hmn Hnp.                         (* omega が使う。 *)
    pose n1 := (n - m)%N.
    pose n2 := (p - n)%N.
    have -> : (p = m + n1 + n2)%N by rewrite /n1 /n2; ssromega.
    have -> : (n = m + n1)%N by rewrite /n1; ssromega.
    by apply: sum_cat'.
  Qed.

End Summation1.

(* END *)
