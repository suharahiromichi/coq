(**
n乗の和の因数分解公式
(factorization formula for the sum of powers n)
===================

@suharahiromichi

2023/07/01
*)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

なんの役に立つかわかりませんが $$ a ^ k + 1 $$ の因数分解を考えてみます。

$$ a ^ k - b ^ k $$ の因数分解は高校で習った通り以下です。

```math
a ^ k - b ^ k = (a - b) \ \sum_{i=0}^{k - 1} (a^i \ b^{k - 1 - i})
```

これは、MathCompのディフォルトである自然数の範囲で可能であり、
``binomial.v`` で証明されています。
*)

Check subn_exp : forall a b k : nat,
    a ^ k - b ^ k = (a - b) * (\sum_(i < k) a ^ (k.-1 - i) * b ^ i).

(**
これの左辺の``-``を``+``に変えた、$$a ^ k - b ^ k$$は、
kが奇数（実際には奇数で割り切れる数）の場合にだけ因数分解できます。
また、aが奇数乗の項が``-``になるため、自然数の範囲では証明できません。
k が奇数で b が 0 の場合ならば、因数分解できるわけです。

```math
a ^ k + 1 = (a + 1) \ \sum_{i=0}^{k - 1} a^i
```

この記事のソースコードは以下にあります。

``https://github.com/suharahiromichi/coq/blob/master/math/ssr_factor_sum_of_power.v``
*)

(**
# 補題

Σ（総和）の式を扱うときに、``\bigop``の補題を直接使ってもよいですが、
わかりやすさのために、``\sum`` について証明しておきます。

## ``a_n``項を取り出す。

$$ \sum_{i=n}^{n}a_i = a_n $$

総和をとる範囲がひとつの項の場合（n以上n以下）は、``a n`` となります。
 *)
  Lemma sum_nat1 n a :
    \sum_(n <= i < n.+1)(a i) = a n.
  Proof. by rewrite big_nat1. Qed.
(*
## 最後の項をΣの外に出す。

n(インデックスの上限)についての帰納法と組み合わせて使います。

$$ \sum_{i=m}^{n}a_i = \sum_{i=m}^{n-1}a_i + a_n $$
 *)
  Lemma sum_last m n a :
    m <= n ->
    \sum_(m <= i < n.+1)(a i) = \sum_(m <= i < n)(a i) + a n.
  Proof.
    move=> Hmn.
    by rewrite big_nat_recr.
  Qed.

(**
式の整理に必要な補題を証明しておきます。

## 補題
*)
Lemma a1_exp a k : 0 < a ->
                   a ^ k.+2 - a ^ k = a.+1 * (a ^ k.+1 - a ^ k).
Proof.
  move=> Ha.
  rewrite -[in RHS]addn1.
  rewrite mulnDl 2!mulnBr.
  rewrite -2!expnS 2!mul1n.
  rewrite addnBA; last rewrite leq_pexp2l //=.
  rewrite subnK; last rewrite leq_pexp2l //=.
  done.
Qed.

(**
# ``k = 2 n + 1`` の場合の証明

説明を補足すること。
*)
Lemma addn1_exp_2n1 a n : 0 < a ->
                      (a ^ n.*2.+1).+1 = a.+1 * (\sum_(0 <= i < n.+1) (a ^ i.*2 - a ^ i.*2.-1)).+1.
Proof.
  elim: n => [| n IHn] Ha.
  - rewrite double0 expn1 sum_nat1 double0 expn0.
    have -> : (1 - 1).+1 = 1 by done.
    by rewrite muln1.
  - rewrite sum_last //.
    rewrite -addSn mulnDr -IHn //.
    rewrite addSn.
    congr _.+1.
    (* a ^ n.+1.*2.+1 = a ^ n.*2.+1 + (a + 1) * (a ^ n.+1.*2 - a ^ n.+1.*2.-1) *)
    rewrite [in a ^ n.+1.*2]doubleS [in a ^ n.+1.*2.-1]doubleS.
    rewrite -a1_exp //.
    rewrite [n.*2.+2.-1]/= doubleS.
    rewrite subnKC //.
    rewrite leq_pexp2l //.
    rewrite -{1}[n.*2]addn0 -addn3.
    by rewrite ltn_add2l.
Qed.

(**
# 応用 1

応用として、kが奇数の時、$$a^k + 1$$ が $$a + 1$$ で割り切れることを証明します。

まず、$$2 \ n + 1$$ で証明したのち、ついで、$$k = 2 \ n + 1$$ で証明します。
*)

Lemma dvd_exp_2n1 a n :
  0 < a -> a.+1 %| (a ^ n.*2.+1).+1.
Proof.
  move=> Ha.
  rewrite addn1_exp_2n1 //.
  by apply: dvdn_mulr.
Qed.

Lemma dvd_exp_odd a k :
  0 < a -> odd k -> a.+1 %| (a ^ k).+1.
Proof.
  move=> Ha Hk.
  rewrite -[k]odd_double_half Hk add1n.  
  by apply: dvd_exp_2n1.
Qed.


(**
# 応用 2

もうひとつの応用として、

$$2 ^ n + 1$$ が素数のとき、$$n$$は2の累乗である。

これの対偶を証明してみます。すなわち、

$$n$$が2の累乗でない（奇数を因数に持つ）とき、$$2 ^ n + 1$$は合成数（ふたつの自然数の積）である。
*)
Lemma expS_composite n : forall (a b : nat),
    0 < a -> n = (2 ^ a) * b.*2.+1 ->
    (exists p q : nat, 1 < p -> 1 < q -> (2 ^ n).+1 = p * q).
Proof.
  move=> a b Ha ->.
  have -> : 2 ^ ((2 ^ a) * b.*2.+1) = (2 ^ (2 ^ a)) ^ b.*2.+1 by rewrite expnM.
  set x := 2 ^ (2 ^ a).
  have Ho : odd b.*2.+1 by rewrite oddS odd_double.
  have Hx : 0 < x  by rewrite expn_gt0 //.
  exists x.+1.
  exists (\sum_(0 <= i < b.+1) (x ^ i.*2 - x ^ i.*2.-1)).+1.
  by rewrite addn1_exp_2n1.
Qed.

(**
# 使わなかった補題
*)

Lemma l_odd_doublenS  k : odd k -> k = k./2.*2.+1.
Proof.
  move=> Hk.
  by rewrite odd_halfK // (@ltn_predK 0) // odd_gt0.
Qed.

Lemma ltnSSn n : n < n.+2.
Proof.
  by apply: (ltn_trans (_ : n < n.+1)); first rewrite ltnSn //.
Qed.

Lemma ltnSSSn n : n < n.+3.
Proof.
  apply: (ltn_trans (_ : n < n.+1)); first rewrite ltnSn //.
  by apply: ltnSSn.
Qed.

(* END *)
