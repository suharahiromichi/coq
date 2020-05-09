From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import ssrinv.
Require Import ssrneg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Goal forall (a b : nat), (a <= b) = false -> b < a.
Proof.
  move=> a b H1.
  find_neg_hypo.
  Check leqNgt : forall m n : nat, (m <= n) = ~~ (n < m).
  Check ltnNge : forall m n : nat, (m < n) = ~~ (n <= m).
  rewrite -ltnNge in H1.
  Search _ (_ <= _).
  done.
Qed.

