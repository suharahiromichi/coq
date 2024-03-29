From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(**
# Rising Factorial 上昇階乗冪
*)
Section DEFINE.
  Fixpoint rfact_rec n m := if m is m'.+1 then n * rfact_rec n.+1 m' else 1.
  
  Definition rising_factorial := nosimpl rfact_rec.
End DEFINE.
  
Notation "n ^^ m" := (rising_factorial n m)
(at level 30, right associativity).

Compute 3 ^^ 2.


Section LEMMAS.
  
  Lemma rfactE : rising_factorial = rfact_rec. Proof. by []. Qed.
  
  Lemma rfactn0 n : n ^^ 0 = 1. Proof. by []. Qed.

  Lemma rfact0n m : 0 ^^ m = (m == 0). Proof. by case: m. Qed.
  
  Lemma rfactnS n m : n ^^ m.+1 = n * n.+1 ^^ m. Proof. by []. Qed.
  
  Lemma rfactn1 n : n ^^ 1 = n. Proof. exact: muln1. Qed.

  Lemma rfactSS n m : n * n.+1 ^^ m.+1 = n ^^ m * (n + m) * (n + m + 1).
  Proof.
    elim: m n => [| m IHm] n.
    - rewrite rfactn0 mul1n addn0 addn1.
      rewrite rfactn1.
      done.
    - rewrite rfactnS.
      rewrite (IHm n.+1).
      rewrite ?mulnA.
      congr (_ * _ * _); by ssromega.
  Qed.
  
  Lemma rfactnSr n m : n ^^ m.+1 = n ^^ m * (n + m).
  Proof.
    elim: m n => [|m IHm] n.
    - rewrite rfactn1.
      by rewrite rfactn0 mul1n addn0.
    - rewrite rfactnS.
      rewrite IHm.
      rewrite mulnA.
      rewrite rfactnS.
      by rewrite addSn addnS.
  Qed.
  
  Compute 0 ^^ 0.                           (* 1 *)
  Compute 0 ^^ 1.                           (* 0 *)
  Compute 0 ^^ 2.                           (* 0 *)
  Compute 1 ^^ 0.                           (* 1 *)
  Compute 1 ^^ 1.                           (* 1 *)
  Compute 1 ^^ 2.                           (* 2 *)
  Compute 2 ^^ 0.                           (* 1 *)
  Compute 2 ^^ 1.                           (* 2 *)
  Compute 2 ^^ 2.                           (* 6 *)
  Compute 2 ^^ 3.                           (* 3 *)
  
  Lemma rfact_gt0 n : (0 < n ^^ 0).
  Proof.
    done.
  Qed.
  
  Lemma rfact_gt0' m : (0 < 0 ^^ m) = (m == 0).
  Proof.
    by case: m.
  Qed.
  
  Lemma rfact_small m : 0 < m -> 0 ^^ m = 0.
  Proof.
    by case: m.
  Qed.
  
  Lemma rfactnn n : 1 ^^ n = n`!.
  Proof.
    elim: n => [|n IHn] //.
    rewrite rfactnSr add1n IHn.
    by rewrite factS mulnC.
  Qed.
  
  Compute 0`! * 0.+1 ^^ 0 = (0 + 0)`!.      (* 0 0 *)
  Compute 1`! * 1.+1 ^^ 0 = (1 + 0)`!.      (* 1 0 *)
  Compute 1`! * 1.+1 ^^ 1 = (1 + 1)`!.      (* 1 1 *)
  Compute 3`! * 3.+1 ^^ 2 = (3 + 2)`!.      (* 3 2 *)
  Compute 2`! * 2.+1 ^^ 3 = (2 + 3)`!.      (* 2 3 *)
  
  Lemma rfact_fact n m : n`! * n.+1 ^^ m = (n + m)`!.
  Proof.
    elim: m n => [| m IHn] n.
    - by rewrite rfactn0 muln1 addn0.
    - rewrite rfactnS.
      have -> : n + m.+1 = n.+1 + m by ssromega.
      rewrite -IHn.
      rewrite !mulnA.
      rewrite factS [n.+1 * n`!]mulnC.
      done.
  Qed.
  
  Compute 0.+1 ^^ 0 = (0 + 0)`! %/ 0`!.     (* 0 0 *)
  Compute 1.+1 ^^ 0 = (1 + 0)`! %/ 1`!.     (* 1 0 *)
  Compute 1.+1 ^^ 1 = (1 + 1)`! %/ 1`!.     (* 1 1 *)
  Compute 3.+1 ^^ 2 = (3 + 2)`! %/ 3`!.     (* 3 2 *)
  Compute 2.+1 ^^ 3 = (2 + 3)`! %/ 2`!.     (* 2 3 *)
  
  Lemma rfact_factd n m : n.+1 ^^ m = (n + m)`! %/ n`!.
  Proof.
    rewrite -rfact_fact.
    rewrite mulnC mulnK; first done.
    by rewrite fact_gt0.
  Qed.
  
  (* ****************************** *)
  (* 上昇階乗冪 と 下降階乗冪 の関係 *)
  (* ****************************** *)
  
  Lemma rfact_ffact n m : n.+1 ^^ m = (n + m) ^_ m.
  Proof.
    elim: m n => [| m IHm] n.
    - by rewrite ffactn0 rfactn0.
    - rewrite rfactnS.
      rewrite ffactnS.
      have -> : (n + m.+1).-1 = n + m by ssromega.
      rewrite -IHm.
      rewrite -rfactnS.
      rewrite [RHS]mulnC.
      have -> : n + m.+1 = m.+1 + n by ssromega.
      rewrite rfactnSr.
      rewrite !addSn [m + n]addnC.
      done.
  Qed.
  
End LEMMAS.

(* END *)
