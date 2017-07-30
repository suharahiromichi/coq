Require Import Div2.
Require Import Arith.
Require Import Omega.

Goal forall n : nat, div2 (S n) < S n.
Proof.
  intros n.
  (* Hintデータベースとしてarithを指定して、Resoluitonをする。 *)
  (* debug *) auto with arith.
Qed.
  
Goal forall n : nat, div2 (S n) < S n.
Proof.
  intros n.  
  (* 上記のautoと同内容を手動でおこなう例。 *)
  Check lt_div2 : forall n : nat, 0 < n -> Nat.div2 n < n.
  apply lt_div2.
  Check Nat.lt_0_succ : forall n : nat, 0 < S n.
  apply Nat.lt_0_succ.
Qed.
  
Goal forall n : nat, div2 (S n) < S n.
Proof.
  intros n.  
  apply lt_div2.
  (* 0 < S n をプレスバーガー算術で解く。 *)
  omega.
Qed.

