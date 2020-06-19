From mathcomp Require Import all_ssreflect.

Require Import ssr_rising_fact.
Require Import ssr_multiset_coefficient.
Require Import ssr_multiset_coef_rising_fact.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(**
# 二項係数 まとめ
*)

Compute 0 ^^ 0.                             (* 1 *)
Compute 0 ^^ 1.                             (* 0 *)
Compute 0 ^^ 2.                             (* 0 *)
Compute 1 ^^ 0.                             (* 1 *)
Compute 1 ^^ 1.                             (* 1 *)
Compute 1 ^^ 2.                             (* 2 *)
Compute 2 ^^ 0.                             (* 1 *)
Compute 2 ^^ 1.                             (* 2 *)
Compute 2 ^^ 2.                             (* 6 *)
Compute 2 ^^ 3.                             (* 3 *)

(* **** *)

Compute 'C(0, 0).                           (* 1 *)
Compute 'C(0, 1).                           (**0**)

Compute 'C(1, 0).                           (* 1 *)
Compute 'C(1, 1).                           (* 1 *)
Compute 'C(1, 2).                           (**0**)
  
Compute 'C(2, 0).                           (* 1 *)
Compute 'C(2, 1).                           (* 2 *)
Compute 'C(2, 2).                           (* 1 *)
Compute 'C(2, 3).                           (**0**)

Compute 'C(3, 0).                           (* 1 *)
Compute 'C(3, 1).                           (* 3 *)
Compute 'C(3, 2).                           (* 3 *)
Compute 'C(3, 3).                           (* 1 *)
Compute 'C(3, 4).                           (**0**)

Compute 'C(4, 0).                           (* 1 *)
Compute 'C(4, 1).                           (* 4 *)
Compute 'C(4, 2).                           (* 6 *)
Compute 'C(4, 3).                           (* 4 *)
Compute 'C(4, 4).                           (* 1 *)
Compute 'C(4, 5).                           (**0**)

(* **** *)

Compute 'H(0, 0).                   (**1**) (* 漸化式では使わない。 *)
Compute 'H(0, 1).                   (* 0 *)
Compute 'H(0, 2).                   (* 0 *)

Compute 'H(1, 0).                           (* 1 *)
Compute 'H(1, 1).                           (* 1 *)
Compute 'H(1, 2).                           (* 1 *)

Compute 'H(2, 0).                           (* 1 *)
Compute 'H(2, 1).                           (* 2 *)
Compute 'H(2, 2).                           (* 3 *)
Compute 'H(2, 3).                           (* 4 *)
Compute 'H(2, 4).                           (* 5 *)
Compute 'H(2, 5).                           (* 6 *)
Compute 'H(2, 6).                           (* 7 *)
Compute 'H(2, 7).                           (* 8 *)
Compute 'H(2, 8).                           (* 9 *)

Compute 'H(3, 0).                           (* 1 *)
Compute 'H(3, 1).                           (* 3 *)
Compute 'H(3, 2).                           (* 6 *)
Compute 'H(3, 3).                           (* 10 *)
Compute 'H(3, 4).                           (* 15 *)
Compute 'H(3, 5).                           (* 21 *)
Compute 'H(3, 6).                           (* 28 *)
Compute 'H(3, 7).                           (* 36 *)
Compute 'H(3, 8).                           (* 45 *)

Compute 'H(4, 0).                           (* 1 *)
Compute 'H(4, 1).                           (* 4 *)
Compute 'H(4, 2).                           (* 10 *)
Compute 'H(4, 3).                           (* 20 *)
Compute 'H(4, 4).                           (* 35 *)
Compute 'H(4, 5).                           (* 56 *)
Compute 'H(4, 6).                           (* 84 *)
Compute 'H(4, 7).                           (* 120 *)
Compute 'H(4, 8).                           (* 165 *)

Section Bin.
  
  Check divn_fact_mul_add_fact : forall n m : nat, n`! * m`! %| (n + m)`!.

  Check ffactn0 : forall n : nat, n ^_ 0 = 1.
  Check ffact0n : forall m : nat, 0 ^_ m = (m == 0).
  Check ffactnS : forall n m : nat, n ^_ m.+1 = n * n.-1 ^_ m.
  Check ffactn1 : forall n : nat, n ^_ 1 = n.
  Check ffactSS : forall n m : nat, n.+1 ^_ m.+1 = n.+1 * n ^_ m.
  Check ffactnSr : forall n m : nat, n ^_ m.+1 = n ^_ m * (n - m).
  Check ffact_gt0 : forall n m : nat, (0 < n ^_ m) = (m <= n).
  Check ffact_small : forall n m : nat, n < m -> n ^_ m = 0.
  Check ffactnn : forall n : nat, n ^_ n = n`!.
  Check ffact_fact : forall n m : nat, m <= n -> n ^_ m * (n - m)`! = n`!.
  Check ffact_factd : forall n m : nat, m <= n -> n ^_ m = n`! %/ (n - m)`!.
  
  Check rfactn0 : forall n : nat, n ^^ 0 = 1.
  Check rfact0n : forall m : nat, 0 ^^ m = (m == 0).
  Check rfactnS : forall n m : nat, n ^^ m.+1 = n * n.+1 ^^ m.
  Check rfactn1 : forall n : nat, n ^^ 1 = n.
  Check rfactSS : forall n m : nat, n * n.+1 ^^ m.+1 = n ^^ m * (n + m) * (n + m + 1).
  Check rfactnSr : forall n m : nat, n ^^ m.+1 = n ^^ m * (n + m).
  Check rfact_gt0 : forall n : nat, 0 < n ^^ 0.               (* notu *)
  Check rfact_gt0' : forall m : nat, (0 < 0 ^^ m) = (m == 0). (* notu *)
  Check rfact_small : forall m : nat, 0 < m -> 0 ^^ m = 0.    (* notu *)
  Check rfactnn : forall n : nat, 1 ^^ n = n`!.
  Check rfact_fact : forall n m : nat, n`! * n.+1 ^^ m = (n + m)`!.
  Check rfact_factd : forall n m : nat, n.+1 ^^ m = (n + m)`! %/ n`!.
  
  Check rfact_ffact : forall n m : nat, n.+1 ^^ m = (n + m) ^_ m.

  (* **** *)

  Check bin0 : forall n : nat, 'C(n, 0) = 1.
  Check bin0n : forall m : nat, 'C(0, m) = (m == 0).
  Check binS : forall n m : nat, 'C(n.+1, m.+1) = 'C(n, m.+1) + 'C(n, m).
  Check bin1 : forall n : nat, 'C(n, 1) = n.
  Check bin_fact : forall n m : nat, m <= n -> 'C(n, m) * (m`! * (n - m)`!) = n`!.
  Check bin_ffact : forall (n m : nat), 'C(n, m) * m`! = n ^_ m.
  Check bin_ffactd : forall (n m : nat), 'C(n, m) = n ^_ m %/ m`!.
  Check mul_bin_diag : forall n m : nat, n * 'C(n.-1, m) = m.+1 * 'C(n, m.+1).
  Check bin_fact : forall n m : nat, m <= n -> 'C(n, m) * (m`! * (n - m)`!) = n`!.
  Check bin_factd : forall n m : nat, 0 < n -> 'C(n, m) = n`! %/ (m`! * (n - m)`!).
  Check bin_ffact : forall n m : nat, 'C(n, m) * m`! = n ^_ m.
  Check bin_ffactd : forall n m : nat, 'C(n, m) = n ^_ m %/ m`!.
  
  (* **** *)
  
  Check multiset_rec_equation.
  Check msc0 : forall n : nat, 'H(n, 0) = 1.
  Check msc0n : forall m : nat, 'H(0, m) = (m == 0).
  Check mscS : forall n m : nat, 'H(n.+1, m.+1) = 'H(n, m.+1) + 'H(n.+1, m).
  Check msc1 : forall n : nat, 'H(n, 1) = n.
  Check msc1n : forall n : nat, 'H(1, n) = 1.
  Check msc_small : forall m : nat, 0 < m -> 'H(0, m) = 0. (* notu *)
  Check mul_msc_diag : forall n m : nat, n * 'H(n.+1, m) = m.+1 * 'H(n, m.+1).
  Check msc_fact : forall n m : nat, 'H(n.+1, m) * n`! * m`! = (n + m)`!.
  Check msc_factd : forall n m : nat, 'H(n.+1, m) = (n + m)`! %/ (n`! * m`!).
  Check msc_ffact : forall n m : nat, 'H(n.+1, m) * m`! = (n + m) ^_ m.
  Check msc_ffactd : forall n m : nat, 'H(n.+1, m) = (n + m) ^_ m %/ m`!.

  Check multiset_binominal : forall n m : nat, 'H(n.+1, m) = 'C(n + m, m).
  
  Check msc_rfact : forall n m : nat, 'H(n, m) * m`! = n ^^ m.
  Check msc_rfactd : forall n m : nat, 'H(n, m) = n ^^ m %/ m`!.
End Bin.

(* END *)
