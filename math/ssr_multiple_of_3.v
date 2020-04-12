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
Section multiple_of_3.

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
  elim: n => [| n IHn].
  - by rewrite 2!big_nat1 l_100x__99x_x.
  - rewrite big_nat_recr //=.
    rewrite [\sum_(1 <= i < n.+3) ((10 ^ i - 1) * x i + x i)]big_nat_recr //=.
    have <- : 10 ^ n.+2 * x n.+2 = (10 ^ n.+2 - 1) * x n.+2 + x n.+2
      by rewrite -{3}[x n.+2]mul1n -[(10 ^ n.+2 - 1) * x n.+2 + 1 * x n.+2]mulnDl
         -l_100__99_1.
      by rewrite -IHn.
Qed.

Lemma s__s_s (n : nat) (F G : nat -> nat) :
  \sum_(1 <= i < n)(F i + G i) = 
  \sum_(1 <= i < n)(F i) + \sum_(1 <= i < n)(G i).
Proof.
  rewrite big_split /=.
  done.
Qed.

Lemma s100x__s99x_sx (n : nat) :
  \sum_(1 <= i < n.+2)(10^i * (x i)) =
  \sum_(1 <= i < n.+2)((10^i - 1) * (x i)) + \sum_(1 <= i < n.+2)(x i).
Proof.
    by rewrite -s__s_s s100x__s99x_x.
Qed.

(**
## 補題 : 10x + 100y + 1000z が3で割りきれることと、
x + y + z が3で割りきれることは、同値である。
 *)
Lemma mo3 (n : nat) : (3 %| \sum_(1 <= i < n.+2)(10^i * (x i))) =
                      (3 %| \sum_(1 <= i < n.+2)(x i)).
Proof.
  rewrite s100x__s99x_sx.
  rewrite dvdn_addr //.
    by apply: dvdn3_s99x.
Qed.

(**
## 定理 : u + 10x + 100y + 1000z が3で割りきれることと、
u + x + y + z が3で割りきれることは、同値である。
 *)

(* *************************** *)
(* *************************** *)


(* 具体的な数についての証明 *)

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

End multiple_of_3.

(* END *)
