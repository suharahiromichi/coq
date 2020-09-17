(**

======

2020_8_22 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import bigop matrix.

Require Import ssromega.
(**
[https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v]


もダウンロードして同じディレクトリに置いて、coqc ssromega.v を実行し、
ssromega.vo ができていることを確認してください。
*)
     
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 問題

 自然数 n が合成数なら、メルセンヌ数 $ M_{n} = 2^{n} - 1 $
も合成数であることを証明してください。

実際には、nが、2以上の任意の2自然数に積であるとき（すなわち合成数であるとき）、
$ 2^{n} -1 $ もふたつの自然数の積（合成数）であることを証明します。

また、合成数の定義は、「それより小さい、ふたつの正の整数の積で表される整数」
ですが、ここでは、「ふたつの 2以上の自然数 の積で表される自然数」としています。
これは同値です（おまけを参照）。


[a] https://ja.wikipedia.org/wiki/メルセンヌ数
 *)
(**
# 証明

## bigop の補題
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

(**
## 補題

最初に補題として、[a] にも掲載されている次式を証明します。
これは、a と b は自然数で、$1 \le a$ であれば成り立ちます。

$$ (2^{b} - 1) \sum_{i=0}^{a-1} 2^{i b} = 2^{a b} - 1, ただし 1 \le a $$
*)
  Lemma l_e2_ab_1 a b :
    1 <= a ->
    (2^b - 1) * (\sum_(0 <= i < a) 2^(i * b)) = 2^(a * b) - 1.
  Proof.
    move=> Ha.
    
    (* 左辺を展開する。 *)
    rewrite mulnBl.
    
    (* 左辺、第1項 *)
    rewrite -sum_distrr //=.
    have H : \sum_(0 <= i < a) 2 ^ b * 2 ^ (i * b) = \sum_(0 <= i < a) 2 ^ (i.+1 * b).
      by apply: eq_sum => i; rewrite -expnD mulnC -mulnS mulnC.
    rewrite H.
    rewrite -(sum_add1 a (fun x => 2 ^ (x * b))).
    rewrite [\sum_(1 <= i < a.+1) 2 ^ (i * b)]sum_last //=.
    (* \sum_(1 <= i < a) 2 ^ (i * b) + 2 ^ (a * b) *)
    
    (* 左辺、第2項 *)
    rewrite  mul1n.
    rewrite [\sum_(0 <= i < a) 2 ^ (i * b)]sum_first //=.
    rewrite mul0n expn0.
    rewrite [1 + \sum_(1 <= i < a) 2 ^ (i * b)]addnC.
    (* - (\sum_(1 <= i < a) 2 ^ (i * b) + 1) = *)
    
    (* 左辺を整理する。 *)
    rewrite subnDl.
    (* 2 ^ (a * b) - 1 *)
    
    (* 左辺と右辺が同じ。 *)
    done.
  Qed.
End BigOp.

(**
## 証明の概要

証明したい命題

「nが、2以上の任意の2自然数に積であるとき
（すなわち合成数であるとき）、$2^{n} - 1$ もふたつの自然数の積（合成数）である」

これをもうすこし噛み砕くと、

aとbが2以上の任意の自然数であるとき、適当な2以上の自然数xとyが存在して、

$$ 2^{a * b} - 1 = x y $$

が成り立つ、ということになります。ここで、 $ n = a b $ としています。

そして、適当な x と y について具体的に以下を代入すると、

```math

x = (2^{b} - 1) \\
y - \sum_{i=0}^{a-1}2^{i b}

```

先に証明した補題の式が得られます。

$$ (2^{b} - 1) \sum_{i=0}^{a-1}2^{i b} = 2^{a b} - 1 $$
*)

(**
## 値の範囲

普通は、これで証明終わり。とするのですが、
2以上のaとbに対して、xとyもまた2以上であることを示すことも忘れてはいけません。
それも、別の補題として証明しておきます。
*)  
Section Composite_Number.
  
  (* 何か所かで使う補題。 *)
  Lemma le2_le1 a : 2 <= a -> 1 <= a.       (* 1 < a -> 0 < a *)
  Proof. move=> H. by rewrite ltnW. Qed.    (* ssromega でも解ける。 *)
  
  (* 2 <= x を証明する補題： *)
  Lemma e2b_1_ge2 b : 2 <= b -> 2 <= 2^b - 1. (* 1 < b -> 1 < 2^b - 1 *)
  Proof.
    move=> H.
    rewrite ltn_subRL addn1.
    rewrite -{1}(expn1 2).
      by rewrite ltn_exp2l.
  Qed.
  
  (* 2 <= y を証明する補題： *)  
  Lemma sum0_2_e2ib a b :
    2 <= a -> 2 <= b -> 2 <= \sum_(0 <= i < a) 2 ^ (i * b).
  Proof.
    move=> Ha Hb.
    rewrite sum_first; last by apply: le2_le1.
    rewrite sum_first; last done.
    have H1 : 1 <= 2 ^ (0 * b) by rewrite mul0n expn0.
    have H2 : 1 <= 2 ^ (1 * b) by rewrite mul1n expn_gt0 orb_idr.
    have H3 : 0 <= \sum_(2 <= i < a) 2 ^ (i * b) by done. (* 0以上は自明。 *)
      by ssromega.
  Qed.
  
(**
## 証明したいもの
 *)
  Lemma e2_ab_1_composite (a b : nat) :
    2 <= a -> 2 <= b ->
    exists (x y : nat), 2 <= x /\ 2 <= y /\ (x * y = 2^(a * b) - 1).
  Proof.
    move=> Ha Hb.
    exists (2 ^ b - 1), (\sum_(0 <= i < a) 2 ^ (i * b)).
    split ; [| split].
    - by apply: e2b_1_ge2.    (* 2 <= x を証明する。 *)
    - by apply: sum0_2_e2ib.  (* 2 <= y を証明する。 *)
    - move/le2_le1 in Ha.     (* 前提を 2 <= a から 1 <= a にする。 *)
        by apply: l_e2_ab_1.  (* x * y = ... を証明する。 *)
  Qed.

(**
# おまけ 合成数の定義についての補題

「ある自然数が、より小さいふたつの自然数の積で表されるとき、
そのふたつの自然数は1より大きい」ということを証明します。
 *)  

(**
「2以上」は、「1を越える」、と表記(Notation)だけが異なります。
「1を越える」ほうが表記として複雑なので、Coqの清書系はそちらをつかいます。
これに留意して、ここでは $1 \lt m$ の方を使います。
*)
  Check 2 <= 10.                            (* 1 < 10 *)
  
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

  Lemma l_composite_hypo (m n : nat) :
    ((m < m * n) && (n < m * n)) = ((1 < m) && (1 < n)).
  Proof.
    apply/andP/andP; case=> Hm Hn; split.
    - by apply: l_nmn_1m Hn.
    - by apply: l_mmn_1n Hm.
    - by apply: l_1m1n_mmn.
    - by apply: l_1m1n_nmn.
  Qed.

End Composite_Number.

(* END *)
