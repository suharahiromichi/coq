From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import ssr_multiset_coefficient.
Require Import ssr_rising_fact.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section RFACT_MC.
  
  Lemma msc_small (m : nat) : 0 < m -> 'H(0, m) = 0. (* notu *)
  Proof.
    by case: m.
  Qed.
  
  Lemma msc_rfact (n m : nat) : 'H(n, m) * m`! = n ^^ m.
  Proof.
    elim: m n => [| m IHm] n.
    - by rewrite msc0 mul1n.
    - rewrite factS mulnA ['H(n, m.+1) * m.+1]mulnC.
      rewrite -mul_msc_diag -mulnA.
        by rewrite IHm.
  Qed.
  
  Lemma msc_rfactd n m : 'H(n, m) = (n ^^ m) %/ m`!.
  Proof.
      by rewrite -msc_rfact mulnK ?fact_gt0.
  Qed.
  
  (* 別証明 *)
  (* ffact に変換して証明する。 *)
  
  Lemma msc_rfactd' n m : 'H(n, m) = (n ^^ m) %/ m`!.  
  Proof.
    move: n m => [[| m] | n m] .
    - done.                                 (* n,m = 0,0 *)
    - rewrite msc0n.                        (* n,m = 0,m.+1 *)
      rewrite rfact0n /=.
        by rewrite div0n.
    - by rewrite rfact_ffact msc_ffactd.    (* n,m = n.+1,m+1 *)
  Qed.

End RFACT_MC.

(* END *)
