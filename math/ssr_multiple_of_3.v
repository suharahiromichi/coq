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

(**
# 証明
*)

Variable x : nat -> nat.

(**
## 補題： 9x, 99x, 999x は3の倍数である。
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
## 補題 : 9x + 99y + 999z は3の倍数である。
 *)

(* これは使わない。 *)
Lemma dvdn3_s99 (n : nat) : 3 %| \sum_(1 <= i < n.+2)(10^i - 1).
Proof.
  elim: n => [| n IHn].
  - by rewrite big_nat1.
  - rewrite big_nat_recr //.
    rewrite dvdn_addl //.
      by apply: dvdn3_99.
Qed.

Lemma dvdn3_s99x (n : nat) : 3 %| \sum_(1 <= i < n.+2)((10^i - 1) * (x i)).
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
## 補題 : 10x + 100y + 1000z = 9x + 99y + 999z + x + y + z
*)

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
  \sum_(1 <= i < n.+2)(10^i * (x i)) =
  \sum_(1 <= i < n.+2)((10^i - 1) * (x i) + (x i)).
Proof.
  Admitted.


Lemma s100x__s99x_sx (n : nat) :
  \sum_(1 <= i < n.+2)(10^i * (x i)) =
  \sum_(1 <= i < n.+2)((10^i - 1) * (x i)) + \sum_(1 <= i < n.+2)(x i).
Proof.
  elim: n => [| n IHn].
  - rewrite !big_nat1.
    rewrite -{3}[x 1]mul1n.
      by rewrite -mulnDl.
  - rewrite big_nat_recr.
    rewrite [\sum_(1 <= i < n.+3) (10 ^ i - 1) * x i]big_nat_recr.
    rewrite [\sum_(1 <= i < n.+3) x i]big_nat_recr.
    rewrite -addnA.
    
  Admitted.

(**
## 補題 : 10x + 100y + 1000z が3で割りきれることと、
x + y + z が3で割りきれることは、同値である。
 *)
Goal forall (n : nat), (3 %| \sum_(1 <= i < n.+2)(10^i * (x i))) =
                       (3 %| \sum_(1 <= i < n.+2)(x i)).
Proof.
  move=> n.
  rewrite s100x__s99x_x.
  rewrite dvdn_addr //.
    by apply: dvdn3_s99x.
Qed.

(**
## 定理 : u + 10x + 100y + 1000z が3で割りきれることと、
u + x + y + z が3で割りきれることは、同値である。
 *)






(*

Lemma test100 x : (3 %| x) = (3 %| 100 * x).
Proof.
  have -> : 100 = 99 + 1 by [].
  rewrite mulnDl mul1n.
  rewrite dvdn_addr => //=.
    by rewrite dvdn_mulr.
Qed.

Lemma test10 x : (3 %| x) = (3 %| 10 * x).
Proof.
  have -> : 10 = 9 + 1 by [].
  rewrite mulnDl mul1n.
  rewrite dvdn_addr => //=.
    by rewrite dvdn_mulr.
Qed.


Goal forall x y z, 3 %| x -> 3 %| y -> 3 %| z ->
                   (3 %| (100 * x + 10 * y + z)).
Proof.
  move=> x y z Hx Hy Hz.
  rewrite dvdn_addl.
  - rewrite dvdn_addl.
    + by rewrite -test100.
    + by rewrite -test10.
  - done.
Qed.  

Goal forall x y z, (3 %| (x + y + z)) = (3 %| (100 * x + 10 * y + z)).
Proof.
Admitted.


Lemma testXY x y : 3 %| x -> 3 %| y -> 3 %| (x + y).
Proof.
  move=> Hx Hy.
    by rewrite dvdn_addl.
Qed.

Goal forall a b x y, 3 %| (a + b) = (3 %| (x + y)).
Proof.
  move=> a b x y.
  apply/idP/idP => H.
  - apply: testXY.
  



(* ******************************** *)


Lemma test2 n : 0 < 10^n.
Proof.
  elim: n => // n IHn.
  rewrite expnS.
  rewrite -{1}(muln0 10).
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
    + Search _ (_ %| _ * _).
        by rewrite dvdn_mulr.
  - apply: test2.
Qed.

Lemma test n : 10 ^ n = 10 ^ n - 1 + 1.
Proof.
  rewrite addn1 subn1 prednK //.
  by apply: test2.
Qed.

Goal forall x n, (3 %| x) = (3 %| 10^n * x).
Proof.
  move=> x n.
  have -> : 10^n = (10^n - 1) + 1 by apply: test.
    by rewrite mulnDl mul1n dvdn_addr // dvdn_mulr // dvdn3_99.
Qed.

Goal forall x, (3 %| x) = (3 %| 10 * x).
Proof.
  move=> x.
  have -> : 10 = 9 + 1 by [].
  rewrite mulnDl mul1n.
  rewrite dvdn_addr => //=.
    by rewrite dvdn_mulr.
Qed.

 *)
  