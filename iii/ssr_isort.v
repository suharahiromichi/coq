(**
プログラミング Coq 証明駆動開発入門(1)
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt8.html

をSSReflectに書き直した。
LocallySorted や Permutation は SSReflect の相当の補題を使っているため、
証明の詳細は原著と異なることに注意してください。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(* Permutation, seq.v *)
Check perm_eq (1::2::3::nil) (2::1::3::nil).
Eval compute in perm_eq (1::2::3::nil) (2::1::3::nil). (* true *)
Eval compute in perm_eq nil nil.                       (* true *)

(* Sorted, path.v *)
Check sorted : forall T : eqType, rel T -> seq T -> bool.
Check leq : nat -> nat -> bool.
Check leq : nat -> nat -> Prop.
Check leq : rel nat : Type.
Check le : nat -> nat -> Prop.
Fail Check le : nat -> nat -> bool.
Fail Check le : rel nat.                    (* rel : Type -> Type *)

Check sorted ltn (1::2::3::nil).
Check sorted leq (1::2::3::nil).
Eval compute in sorted leq (1::2::3::nil). (* true *)
Eval compute in sorted leq (3::nil).       (* true *)
Eval compute in sorted leq nil.            (* true *)
Eval compute in sorted leq (2::1::3::nil). (* false *)

(* ソート処理の定義 *)
Fixpoint insert (a : nat)(l : list nat) : list nat :=
  match l with
  | nil => a :: nil
  | x :: xs => if leq a x then a :: l else x :: insert a xs
  end.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | x :: xs => insert x (insertion_sort xs)
  end.

Eval compute in insert 1 nil.                      (* [:: 1] *)
Eval compute in insert 5 [:: 1; 4; 2; 9; 3].       (* [:: 1; 4; 2; 5; 9; 3] *)
Eval compute in insertion_sort [:: 2; 4; 1; 5; 3]. (* [:: 1; 2; 3; 4; 5] *)

(* 証明 *)
Lemma perm_iff : forall (m n : seq nat),
                   (forall l, perm_eq m l = perm_eq n l) <-> perm_eq m n.
Proof.
  move=> m n.
  split=> H.
  - by rewrite H.
  - by apply/perm_eqlP.
Qed.

Lemma perm_swap : forall (l l' : seq nat) (x a : nat),
                    perm_eq [:: x, a & l] l' = perm_eq [:: a, x & l] l'.
Proof.
  move=> l l' x a.
  apply perm_iff.
  Check cat1s.
  rewrite -[[:: x, a & l]]cat1s.
  rewrite -[[:: a & l]]cat1s.
  rewrite -[[:: a, x & l]]cat1s.
  rewrite -[[:: x & l]]cat1s.
  apply/perm_eqlP.
  by apply (perm_catCA [:: x] [:: a] l).
Qed.

Lemma insert_perm : forall (l : seq nat) (x : nat),
                      perm_eq (x::l) (insert x l).
Proof.
  elim=> [x | a l H x //=].
  - by [].
  - case: (x <= a) => [//= |].
    + apply perm_iff => l'.
      rewrite perm_swap.
      apply perm_iff.
      rewrite perm_cons.
      by [].
Qed.

Theorem isort_permutation : forall (l : list nat), perm_eq l (insertion_sort l).
Proof.
  elim=> [| a l H //=].
  - by [].
  - apply perm_eq_trans with (a :: insertion_sort l).
    + by rewrite perm_cons.
    + by apply insert_perm.
Qed.

Lemma sorted_consn : forall (a b : nat) (l : seq nat),
                     sorted leq (b :: l) ->
                     leq a b -> sorted leq (a :: b :: l).
Admitted.

Lemma sotred_cons1 : forall (a : nat), sorted leq (a :: nil).
Admitted.

Lemma insert_sorted : forall (a : nat) (l : list nat),
                        sorted leq l -> sorted leq (insert a l).
Proof.
  move=> a.
  elim=> [| a0 l IHl H /=].
  - by [].
  - case Heqb : (leq a a0).                 (* remember *)
    + apply sorted_consn.
      * by apply H.
      * by rewrite Heqb.
    + admit.                                (* XXXX *)
Qed.

Theorem isort_sorted : forall (l : list nat), sorted leq (insertion_sort l).
Proof.
  elim=> [| a l H //=].
  - by [].
  - by apply insert_sorted.
Qed.

(* END *)

