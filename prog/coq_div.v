(* https://coq.inria.fr/refman/Reference-Manual027.html *)
(* PROGRAM-ing Finger Trees in COQ *)

Require Import Omega.
Require Import List.
Require Import Arith.
Require Import Program.

Set Implicit Arguments.

Program Definition id (n : nat) : { x : nat | x = n } :=
  if dec (leb n 0) then
    0
  else
    S (pred n).
Obligation 1.
Proof.                                      (* n <= 0 -> n = 0 *)
  destruct n.
  - now auto.                               (* n = 0 *)
  - now inversion H.                        (* n >= 1 矛盾 *)

  Restart.
  now destruct n.
Defined.
Obligation 2.
Proof.
  now destruct n.
Defined.


(* DIV2 *)
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
  | S (S p) => S (div2' p)
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
