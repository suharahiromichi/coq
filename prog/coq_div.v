(* https://coq.inria.fr/refman/Reference-Manual027.html *)
(* PROGRAM-ing Finger Trees in COQ *)

Require Import Omega.
Require Import List.
Require Import Arith.
Require Import Arith.Even.
Require Import Program.
Require Import Cpdt.CpdtTactics Cpdt.Coinductive.

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

(* Even *)

Lemma even_2 x : even (x * 2).
Proof.
Admitted.

Lemma odd_2 x : odd (x + x) -> False.
Proof.
Admitted.

Lemma even_2_1 x : even (x + x + 1) -> False.
Proof.
Admitted.

Hint Resolve even_2.

Program Definition div2_2 (n : nat) :
  { m : nat | even m } :=
  div2 n * 2.
(* Obligation なし。 *)

Program Definition div2_2' (n : nat) :
  { m : nat | (even n -> n = m) /\ (odd n -> n - 1 = m) } :=
  div2 n * 2.
Obligation 1.
Proof.
  remember (div2 _).
  remember (_ * 2).
  destruct s as [m H].
  destruct H as [H1 | H2]; simpl in *.
  - split.
    + omega.
    + clear Heqs.
      rewrite <- plus_n_O in H1.
      intro H.
      rewrite H1 in H.
      now apply odd_2 in H.
  - split.
    + clear Heqs.
      rewrite <- plus_n_O in H2.
      intro H.
      rewrite H2 in H.
      now apply even_2_1 in H.
    + omega.
Defined.

(* div2 の末尾再帰版をつくる。 *)

(* END *)
