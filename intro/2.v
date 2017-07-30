(** ProofCafe Coq入門 #2 *)
(** 2017/8/19 @suharahiromichi  *)

Set Implicit Arguments.

(* 自然数 *)
Require Import Arith.

Goal forall x y z : nat, x * (y * z) = x * y * z.
Proof.
  intros.
  now rewrite mult_assoc.
Qed.

Goal forall x : nat, 1 * x = x.
Proof.
  intros.
  now rewrite mult_1_l.
Qed.

Goal forall x : nat, x * 1 = x.
Proof.
  intros.
  now rewrite mult_1_r.  
Qed.

(* 整数 *)
Require Import ZArith.
Open Scope Z.

Goal forall x y z : Z, x * (y * z) = x * y * z.
Proof.
  intros.
  ring.
Qed.
  
Goal forall x : Z, 1 * x = x.
Proof.
  intros.
  ring.
Qed.

Goal forall x : Z, x * 1 = x.
Proof.
  intros.
  ring.
Qed.

(* END *)
