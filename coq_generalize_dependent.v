(*
   generalize dependent m.
   または、intro で「forall m」を残した状態で、
   induction n をする例
*)


Require Import Omega.
Require Import NArith.
Require Import Arith.


Fixpoint sum n :=
  match n with
    | O => O
    | S n' => S n' + sum n'
  end.


Theorem Sum_of_nat : forall (n m: nat),
  m = 2 * sum n -> m = n * (n + 1).
Proof.
  intros n m.
  induction n.
  simpl.
  auto.
  (*
     IHn : m = 2 * sum n -> m = n * (n + 1)
     ============================
     m = 2 * sum (S n) -> m = S n * (S n + 1)
   *)
Abort.


Theorem Sum_of_nat : forall (n m: nat),
  m = 2 * sum n -> m = n * (n + 1).
Proof.
  intro n.
  induction n.
  simpl.
  auto.
  
(*
   n : nat
   IHn : forall m : nat, m = 2 * sum n -> m = n * (n + 1)
   ============================
   forall m : nat, m = 2 * sum (S n) -> m = S n * (S n + 1)
*)
  intros.
  
  (* 代数的な式の変形をする *)
  subst.
  unfold sum.
  fold sum.
  ring_simplify.
  cut (forall m n, m = n -> m + 2 = n + 2).
  intros.
  apply (H (2 * n + 2 * sum n) (n * n + 3 * n)).
  cut (forall x y n, x = y + n -> 2 * n + x = y + 3 * n).
  intros.
  apply (H0 (2 * sum n) (n * n)).
  cut (forall m n, m = n * (n + 1) -> m = n * n + n).
  intros.
  apply H1.
  
  apply IHn.                                (* ここで、上記の前提をつかう！ *)
  reflexivity.                              (* 証明終了！ *)
  
  (* cutで導入した前提を片付ける *)
  intros.
  rewrite H1.
  ring.
  intros.
  rewrite H0.
  ring.
  intros.
  rewrite H.
  reflexivity.
Qed.


Theorem Sum_of_nat' : forall (m n : nat),
  m = 2 * sum n -> m = n * (n + 1).
Proof.
  intros m n.
  generalize dependent m.
  induction n.
  simpl.
  auto.


(*
   n : nat
   IHn : forall m : nat, m = 2 * sum n -> m = n * (n + 1)
   ============================
   forall m : nat, m = 2 * sum (S n) -> m = S n * (S n + 1)
   
   Sum_of_nat と同じようにする。
*)
Abort.




(* 1変数の場合 *)


Lemma Sample_of_unfold : forall n, 2 * sum n = n * (n + 1).
Proof.
  induction n.
  reflexivity.
  (*
     ここで、sum を unfold して、fold すると式が少し変形されます。
     *)
  unfold sum.
  fold sum.
  (*
     ここでreplaceを使ってちょっと左辺を書き換えます。書き換えて良い証明はsubgoal 2と後回しです。
     *)
  replace (2 * (S n + sum n)) with (2 * S n + 2 * sum n).
  (*
     ここでIHnを用いて書き換えて式変形を ring で自動証明します。後回しにしたものもringで一発です。
     *)
  rewrite IHn.
  ring.
  ring.
Qed.


(* END *)
