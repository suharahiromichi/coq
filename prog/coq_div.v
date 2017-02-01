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

(* 証明なし *)
Fixpoint div2'' (n : nat) : nat :=
  match n with
  | S (S p) => S (div2'' p)
  | _ => O
  end.

(* **** *)
(* Even *)
(* **** *)
(* Hint Constructos even odd with arith *)

Lemma not_odd_and_even n : odd n -> even n -> False.
Proof.
  induction n.
  - now intros Ho He.
  - intros Ho He.
    inversion Ho.
    inversion He.
    now auto.
    
  Restart.
  intros Ho He.
  generalize He Ho.
  now apply not_even_and_odd.
Qed.

Lemma not_odd_2 x : odd (x + x) -> False.
Proof.
  apply not_even_and_odd.
  cutrewrite (x + x = 2 * x).
  - now apply even_mult_l; auto with arith.
  - omega.
Qed.

Lemma not_even_2_1 x : even (x + x + 1) -> False.
Proof.
  apply not_odd_and_even.
  apply odd_plus_r.
  - cutrewrite (x + x = 2 * x).
    + now apply even_mult_l; auto with arith.
    + omega.
  - now auto with arith.
Qed.

Lemma even_2 x : even (x * 2).
Proof.
  apply even_mult_r.
  now auto with arith.
Qed.
Hint Resolve even_2.

Program Definition div2_2' (n : nat) :
  { m : nat | even m } :=
  div2 n * 2.
(* Obligation なし。 *)

Program Definition div2_2 (n : nat) :
  { m : nat | (even n -> n = m) /\ (odd n -> n - 1 = m) } :=
  div2 n * 2.
Obligation 1.
Proof.
  remember (div2 _).
  remember (_ * 2).
  destruct s as [m H].                      (* 証明のないdiv2'' だと s が出てこない。 *)
  destruct H as [H1 | H2]; simpl in *.
  - split.
    + omega.
    + clear Heqs.
      rewrite <- plus_n_O in H1.
      intro H.
      rewrite H1 in H.
      now apply not_odd_2 in H.
  - split.
    + clear Heqs.
      rewrite <- plus_n_O in H2.
      intro H.
      rewrite H2 in H.
      now apply not_even_2_1 in H.
    + omega.
Defined.

Eval compute in  ` (div2_2 4).              (* 4 *)
Eval compute in  ` (div2_2 5).              (* 4 *)

(* 次にやること。 *)
(* div2 の末尾再帰版をつくる。 *)

(* END *)
