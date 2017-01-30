(* https://coq.inria.fr/refman/Reference-Manual027.html *)
(* PROGRAM-ing Finger Trees in COQ *)

Require Import Omega.
Require Import List.
Require Import Arith.
Require Import Program.

Set Implicit Arguments.

Program Fixpoint div2 (n : nat) {measure n} :
  { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
  match n with
  | S (S p) => S (div2 p)
  | _ => O
  end.
Obligation 2.
Proof.
  remember (div2 _ _).
  destruct s as [n H]; simpl.
  omega.
Defined.
Obligation 3.
Proof.
  destruct n as [| n].
  - now left.                               (* n = 0 *)
  - destruct n as [| n].
    + now right.                            (* n = 1 *)
    + induction (H n).
      reflexivity.                          (* n >= 2 *)
      
  Restart.
  destruct n as [| n]; try auto.
  destruct n as [| n]; try auto.
  induction (H n); auto.
Defined.

(* measure なしの場合 *)
Program Fixpoint div2' (n : nat) :
  { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
  match n with
  | S (S p) => S (div2 p)
  | _ => O
  end.
Obligation 1.
Proof.
  omega.
Defined.
Obligation 2.
Proof.
  destruct n as [| n].
  - now left.                               (* n = 0 *)
  - destruct n as [| n].
    + now right.                            (* n = 1 *)
    + induction (H n).
      reflexivity.                          (* n >= 2 *)
      
  Restart.
  destruct n as [| n]; try auto.
  destruct n as [| n]; try auto.
  induction (H n); auto.
Defined.

(* END *)
