(**
プログラミング Coq --- 自然数を扱う

http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt4.html
をSSReflectに書き直した。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Goal forall (n : nat), n = n + 0.
Proof.
  by [].
Qed.

Goal forall (n : nat),
       (exists m : nat, n = m * 4) -> exists k : nat, n = k * 2.
Proof.
  move=> n.
  elim=> m H.               (* 仮定の H : exists m : nat, n = m * 4 を H : n = x * 4 に *)
  exists (m * 2).           (* サブゴールの exists に x * 2 を与える *)
  by rewrite -mulnA.        (* x * 2 * 2 を x * (2 * 2) に *)
Qed.

Theorem lt_Snm_nm : forall (n m : nat), S n < m -> n < m.
Proof.
  move=> n m H.
  Check @ltn_trans n.
  apply: (@ltn_trans (S n)).                (* 最初の引数が m < n < p の n  *)
  + by apply ltnSn.
  + by [].
Qed.

(* 前回の答え *)

Theorem rev_involute : forall (A : Type)(l : seq A), rev (rev l) = l.
Proof.
  move=> A.
  elim=> [//= | a l IHl].
  rewrite -cat1s 2!rev_cat.
  by rewrite IHl.
Qed.

Theorem fold_right_app : forall (A B : Type) (f : B -> A -> A) (l l' : seq B) (i : A),
      foldr f i (l ++ l') = foldr f (foldr f i l') l.
Proof.
  move=> A B f l l' i.
  elim: l => [//= | a l IHl /=].
  by congr (f a _).
Qed.

(* END *)
