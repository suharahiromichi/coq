(**
メルセンヌ数の基本定理の証明
==================

2020_9_19 @suharahiromichi
*)

(**
# はじめに

「メルセンヌ数 $M_{p}$ が素数のとき、pは素数である」という、
メルセンヌ数の基本定理を証明します。
この命題は、「逆」が成り立たないことで有名ですが、
実際の証明では対偶を証明することになります。


ソースコードは以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_composite_number.v
 *)

From mathcomp Require Import all_ssreflect.

Require Import ssromega.
(**
https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v

もダウンロードして同じディレクトリに置いて、coqc ssromega.v を実行し、
ssromega.vo ができていることを確認してください。
*)
     
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 問題

自然数 n が合成数なら、メルセンヌ数 $ M_{n} = 2^{n} - 1 $
も合成数であることを証明します。

実際には、nが、1を越える任意の2自然数に積であるとき（すなわち合成数であるとき）、
$ 2^{n} -1 $ もふたつの自然数の積（合成数）であることを証明します。

また、合成数の定義は、「それより小さい、ふたつの正の整数の積で表される整数」
ですが、ここでは、「ふたつの 1を越える自然数 の積で表される自然数」としています。
これは同値です（おまけを参照）。
 *)
(**
# 証明

## bigop の補題

MathComp の ``bigop.v`` の補題のうちのいくつかを使いやすい命題にしておきます。
*)
Section BigOp.
  Lemma eq_sum m n a b : a =1 b ->
                         \sum_(m <= i < n)(a i) = \sum_(m <= j < n)(b j).
  Proof.
    move=> Hab.                             (* =1 は第1階の=です。 *)
    apply: eq_big_nat => i Hmn.
      by rewrite Hab.
  Qed.

  Lemma sum_distrr m n c a :
    m < n ->
    \sum_(m <= i < n)(c * (a i)) = c * (\sum_(m <= i < n)(a i)).
  Proof. by rewrite big_distrr. Qed.

  Lemma sum_add1 n a :
    \sum_(1 <= i < n.+1)(a i) = \sum_(0 <= i < n)(a i.+1).
  Proof. by rewrite big_add1 succnK. Qed.

  Lemma sum_first m n a :
    m < n ->
    \sum_(m <= i < n)(a i) = a m + \sum_(m.+1 <= i < n)(a i).
  Proof.
    move=> Hn.
      by rewrite big_ltn.
  Qed.

  Lemma sum_last m n a :
    m <= n ->
    \sum_(m <= i < n.+1)(a i) = \sum_(m <= i < n)(a i) + a n.
  Proof.
    move=> Hmn.
      by rewrite big_nat_recr.
  Qed.
End BigOp.

(**
## 補題

最初に補題として、[a] にも掲載されている次式を証明します。
これは、a と b は自然数で、$1 \le a$ であれば成り立ちます。

$$ (2^{b} - 1) \sum_{i=0}^{a-1} 2^{i b} = 2^{a b} - 1, ただし 1 \le a $$
*)
Section Composite_Number.
  
  Lemma l_e2_ab_1 a b :
    1 <= a ->
    (2^b - 1) * (\sum_(0 <= i < a) 2^(i * b)) = 2^(a * b) - 1.
  Proof.
    move=> Ha.
    
    (* 左辺を展開する。 *)
    rewrite mulnBl.
    
    (* 左辺、第1項 *)
    rewrite -sum_distrr //=.
    have -> : \sum_(0 <= i < a) 2 ^ b * 2 ^ (i * b) = \sum_(0 <= i < a) 2 ^ (i.+1 * b)
      by apply: eq_sum => i; rewrite -expnD mulnC -mulnS mulnC.
    rewrite -(sum_add1 a (fun x => 2 ^ (x * b))).
    rewrite [\sum_(1 <= i < a.+1) 2 ^ (i * b)]sum_last //=.
    (* \sum_(1 <= i < a) 2 ^ (i * b) + 2 ^ (a * b) *)
    
    (* 左辺、第2項 *)
    rewrite  mul1n.
    rewrite [\sum_(0 <= i < a) 2 ^ (i * b)]sum_first //=.
    rewrite mul0n expn0.
    rewrite [1 + \sum_(1 <= i < a) 2 ^ (i * b)]addnC.
    (* - (\sum_(1 <= i < a) 2 ^ (i * b) + 1) *)
    
    (* 左辺を整理する。 *)
    rewrite subnDl.
    (* 2 ^ (a * b) - 1 *)
    
    (* 左辺と右辺が同じ。 *)
    done.
  Qed.

(**
## 証明の概要

証明したい命題
「nが、1を越える任意の2自然数に積であるとき
（すなわち合成数であるとき）、$2^{n} - 1$ もふたつの自然数の積（合成数）である」

これをもうすこし噛み砕くと、
aとbが1を越える任意の自然数であるとき、適当な1を越える自然数xとyが存在して、

$$ 2^{a b} - 1 = x y $$

が成り立つ、ということになります。ここで、 $ n = a b $ としています。

そして、適当な x と y について具体的に以下を代入すると、

```math

x = 2^{b} - 1 \\
y = \sum_{i=0}^{a-1}2^{i b}

```

先に証明した補題の式が得られます。

$$ (2^{b} - 1) \sum_{i=0}^{a-1}2^{i b} = 2^{a b} - 1 $$
*)

(**
## 値の範囲

普通は、これで「証明終わり。」とするのですが、
1を越えるaとbに対して、xとyもまた1を越えるであることを示すことも忘れてはいけません。
それも、別の補題として証明しておきます。
*)  
  (* 何か所かで使う補題。 *)
  Lemma lt1_le1 a : 1 < a -> 1 <= a.       (* 1 < a -> 1 <= a *)
  Proof. move=> H. by rewrite ltnW. Qed.   (* ssromega でも解ける。 *)
  
  (* 1 < x を証明する補題： *)
  Lemma e2b_1_ge2 b : 1 < b -> 1 < 2^b - 1. (* 1 < b -> 1 < 2^b - 1 *)
  Proof.
    move=> H.
    rewrite ltn_subRL addn1.
    rewrite -{1}(expn1 2).
      by rewrite ltn_exp2l.
  Qed.
  
  (* 1 < y を証明する補題： *)  
  Lemma sum0_2_e2ib a b :
    1 < a -> 1 < b -> 1 < \sum_(0 <= i < a) 2 ^ (i * b).
  Proof.
    move=> Ha Hb.
    rewrite sum_first; last by apply: lt1_le1.
    rewrite sum_first; last done.
    have H1 : 1 <= 2 ^ (0 * b) by rewrite mul0n expn0.
    have H2 : 1 <= 2 ^ (1 * b) by rewrite mul1n expn_gt0 orb_idr.
    have H3 : 0 <= \sum_(1 <= i < a) 2 ^ (i * b) by done. (* 0以上は自明。 *)
      by ssromega.
  Qed.
  
(**
## 証明したいもの
 *)
  Lemma mersenne_composite (a b : nat) :
    1 < a -> 1 < b ->
    exists (x y : nat), 1 < x /\ 1 < y /\ (x * y = 2^(a * b) - 1).
  Proof.
    move=> Ha Hb.
    exists (2 ^ b - 1), (\sum_(0 <= i < a) 2 ^ (i * b)).
    split ; [| split].
    - by apply: e2b_1_ge2.    (* 1 < x を証明する。 *)
    - by apply: sum0_2_e2ib.  (* 1 < y を証明する。 *)
    - move/lt1_le1 in Ha.     (* 前提を 1 < a から 1 <= a にする。 *)
        by apply: l_e2_ab_1.  (* x * y = ... を証明する。 *)
  Qed.

(**
# おまけ - 合成数の定義についての補題

「ある自然数が、より小さいふたつの自然数の積で表されるとき、
そのふたつの自然数は1より大きい」ということを証明します。
 *)  
  Lemma l_1m1n_mmn (m n : nat) : 1 < m -> 1 < n -> m < m * n.
  Proof.
    move=> Hm Hn.
    rewrite ltn_Pmulr //.
      by ssromega.                          (* 1 < m -> 0 < m *)
  Qed.
  
  Lemma l_1m1n_nmn (m n : nat) : 1 < m -> 1 < n -> n < m * n.
  Proof.
    move=> Hm Hn.
    rewrite ltn_Pmull //.
      by ssromega.                          (* 1 < n -> 0 < n *)
  Qed.
  
  Lemma l_nmn_1m (m n : nat) : n < m * n -> 1 < m.
  Proof.
    rewrite -{1}[n]mul1n ltn_mul2r.
      by case/andP.
  Qed.
  
  Lemma l_mmn_1n (m n : nat) : m < m * n -> 1 < n.
  Proof.
    rewrite -{1}[m]muln1 ltn_mul2l.
      by case/andP.
  Qed.

(**
以上をまとめると、次のようになります。但し、不使用です。
*)  
  Lemma l_composite_hypo (m n : nat) :
    ((m < m * n) && (n < m * n)) = ((1 < m) && (1 < n)).
  Proof.
    apply/andP/andP; case=> Hm Hn; split.
    - by apply: l_nmn_1m Hn.
    - by apply: l_mmn_1n Hm.
    - by apply: l_1m1n_mmn.
    - by apply: l_1m1n_nmn.
  Qed.

(**
前提を書き直した命題で証明してみます。
*)  
  Lemma mersenne_composite' (a b : nat) :
    a < a * b -> b < a * b ->
    exists (x y : nat), x < x * y /\ y < x * y /\ (x * y = 2^(a * b) - 1).
  Proof.
    move/l_mmn_1n => Hb.
    move/l_nmn_1m => Ha.
    exists (2 ^ b - 1), (\sum_(0 <= i < a) 2 ^ (i * b)).
    split ; [| split].
    - apply/l_1m1n_mmn.
      + by apply: e2b_1_ge2.                (* 1 < x を証明する。 *)
      + by apply: sum0_2_e2ib.              (* 1 < y を証明する。 *)

    - apply/l_1m1n_nmn.
      + by apply: e2b_1_ge2.                (* 1 < x を証明する。 *)
      + by apply: sum0_2_e2ib.              (* 1 < y を証明する。 *)
        
    - move/lt1_le1 in Ha.      (* 前提を 1 < a から 1 <= a にする。 *)
        by apply: l_e2_ab_1.   (* x * y = ... を証明する。 *)
  Qed.
  
End Composite_Number.

(**
# 参考文献

[a] https://ja.wikipedia.org/wiki/メルセンヌ数
*)

(* END *)
