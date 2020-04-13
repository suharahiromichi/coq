(**
10進各桁の和が3の倍数なら、3の倍数であることの証明
========================

@suharahiromichi

2020/04/10
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section multiple_of_3.

(**
# 問題
*)

(**
任意の自然数が3の倍数であることと、
その数を10進数で表したときの各桁の和が3の倍数であることは同値である。

たとえば、2019 は 3の倍数で、2+0+1+9=12 も3の倍数ですが、
2020 は3の倍数でなく、2+0+2+0+4 も3の倍数ではありません。
*)

(**
10進数の数値の各桁を ... x3 x2 x1 x0 で表すとします。
*)
Variable x : nat -> nat.

(**
``0*x0 + 10*x1 + 100*x2 + 1000*x3 + ...`` が3で割り切れることと、
``x0 + x1 + x2 + x3 + ...`` が3で割り切れることが、同値であることを証明します。

MathComp では、x が3で割り切れることを ``3 %| x`` で表します。
割る数の3が前なのに注意してください。これはbool値の述語です。

同値であるとは、bool値が等しいこと（どちらもtrueか、どちらもfalse）で表します。

数列の和 ``Σ(i=0..n)(x i)`` は、big operator を使って``\sum_(0 <= i < n.+1)(x i)``
となります。
``\sum_`` は、演算子と単位元を組み合わせた ``\bigop[addn/0]`` の略記です。

以上から、
*)

Check forall (n : nat), (3 %| \sum_(0 <= i < n.+1)(10^i * (x i))) =
                        (3 %| \sum_(0 <= i < n.+1)(x i)).

(**
を証明すればよいことになります。
以下において、0 は 3の倍数であるとします。
*)

(**
# 証明
*)

(**
## 補題 : ``0*x0 + 9*x1 + 99*x2 + 999*x3`` は3の倍数である。

0, 9, 99, 999 に、任意の自然数 xi を掛けたものの和が、3の倍数になることを証明します。
*)

Lemma gt_exp m n : 0 < m -> 0 < m^n.
Proof.
  move=> H.
  elim: n => // n IHn.
  rewrite expnS.
  rewrite -{1}(muln0 m).
    by rewrite ltn_pmul2l.
Qed.

Lemma dvdn3_99 n : 3 %| (10^n - 1).
Proof.
  elim: n => //.
  move=> n IHn.
  rewrite expnS.
  have {1}-> : 10 = 9 + 1 by [].
  rewrite mulnDl.
  rewrite mul1n.
  rewrite -addnBA.
  - rewrite dvdn_addr.
    + done.
    + by rewrite dvdn_mulr.
  - by apply: gt_exp.
Qed.

Lemma dvdn3_99x n : 3 %| (10^n - 1) * (x n).
Proof.
  rewrite dvdn_mulr //.
    by apply: dvdn3_99.
Qed.

(**
0*x0, 9*x1, 99*x2 が3の倍数であることが判ったので、
これをつかって、補題を証明します。
 *)

Lemma dvdn3_s99x (n : nat) : 3 %| \sum_(0 <= i < n.+1)((10^i - 1) * (x i)).
Proof.
  elim: n => [| n IHn].
  - rewrite big_nat1.
    apply: dvdn_mulr.
      by apply: dvdn3_99.
  - rewrite big_nat_recr //.
    + rewrite dvdn_addl //.
      rewrite dvdn_mulr //.
        by apply: dvdn3_99.
Qed.

(**
## 補題 : 
``x + 10*x1 + 100*x2 + 1000*x3 = (0*x0 + 9*x1 + 99*x2 + 999*x3) + (x0 + x1 + x2 + x3)``

数列の和の問題として、``x + 10*x1 + 100*x2 + 1000*x3`` が、
``0*x0 + 9*x1 + 99*x2 + 999*x3`` と``x0 + x1 + x2 + x3`` の和であることを証明します。

これは一見自明ですが、``Σ(f + g) = Σf + Σg`` を使うために式を変形していきます。

``Σ(f + g) = Σf + Σg`` は、bigop.v のなかで、
可換なop一般に対して証明されているので、それを使います。
*)

Check big_split
  : forall (R : Type) (idx : R) (op : Monoid.com_law idx) 
           (I : Type) (r : seq I) (P : pred I) (F1 F2 : I -> R),
    \big[op/idx]_(i <- r | P i) op (F1 i) (F2 i) =
    op (\big[op/idx]_(i <- r | P i) F1 i) (\big[op/idx]_(i <- r | P i) F2 i).


Lemma l_100__99_1 (n : nat) : 10 ^ n = 10 ^ n - 1 + 1.
Proof.
  rewrite addn1 subn1 prednK //.
    by apply: gt_exp.
Qed.

Lemma l_100x__99x_x (i : nat) : 10^i * (x i) = (10^i - 1) * (x i) + (x i).
Proof.
  rewrite -{3}[(x i)]mul1n.
  rewrite -mulnDl.
    by rewrite -l_100__99_1.
Qed.

Lemma s100x__s99x_x (n : nat) :
  \sum_(0 <= i < n.+1)(10^i * (x i)) =
  \sum_(0 <= i < n.+1)((10^i - 1) * (x i) + (x i)).
Proof.
  elim: n => [| n IHn].
  - by rewrite 2!big_nat1 l_100x__99x_x.
  - rewrite big_nat_recr //=.
    rewrite [\sum_(0 <= i < n.+2) ((10 ^ i - 1) * x i + x i)]big_nat_recr //=.
    have <- : 10 ^ n.+1 * x n.+1 = (10 ^ n.+1 - 1) * x n.+1 + x n.+1
      by rewrite -{3}[x n.+1]mul1n -[(10 ^ n.+1 - 1) * x n.+1 + 1 * x n.+1]mulnDl
         -l_100__99_1.
      by rewrite -IHn.
Qed.

Lemma s__s_s (n : nat) (F G : nat -> nat) :
  \sum_(0 <= i < n)(F i + G i) = 
  \sum_(0 <= i < n)(F i) + \sum_(0 <= i < n)(G i).
Proof.
  rewrite big_split /=.
  done.
Qed.

Lemma s100x__s99x_sx (n : nat) :
  \sum_(0 <= i < n.+1)(10^i * (x i)) =
  \sum_(0 <= i < n.+1)((10^i - 1) * (x i)) + \sum_(0 <= i < n.+1)(x i).
Proof.
    by rewrite -s__s_s s100x__s99x_x.
Qed.

(**
## 定理 : ``x + 10*x1 + 100*x2 + 1000*x3`` が3で割りきれることと、
``x0 + x1 + x2 + x3`` が3で割りきれることは、同値である。

二つの補題をつかって、定理を証明します。
 *)

Theorem mo3 (n : nat) : (3 %| \sum_(0 <= i < n.+1)(10^i * (x i))) =
                      (3 %| \sum_(0 <= i < n.+1)(x i)).
Proof.
  rewrite s100x__s99x_sx.
  rewrite dvdn_addr //.
    by apply: dvdn3_s99x.
Qed.

(* *************************** *)
(* 予備の補題                  *)
(* *************************** *)

Lemma test100 (x2 : nat) : (3 %| x2) = (3 %| 100 * x2).
Proof.
  have -> : 100 = 99 + 1 by [].
  rewrite mulnDl mul1n.
  rewrite dvdn_addr => //=.
    by rewrite dvdn_mulr.
Qed.

Lemma test10 x1 : (3 %| x1) = (3 %| 10 * x1).
Proof.
  have -> : 10 = 9 + 1 by [].
  rewrite mulnDl mul1n.
  rewrite dvdn_addr => //=.
    by rewrite dvdn_mulr.
Qed.

Lemma dvdn3_s99 (n : nat) : 3 %| \sum_(0 <= i < n.+1)(10^i - 1).
Proof.
  elim: n => [| n IHn].
  - by rewrite big_nat1.
  - rewrite big_nat_recr //.
    rewrite dvdn_addl //.
      by apply: dvdn3_99.
Qed.

End multiple_of_3.

(* END *)
