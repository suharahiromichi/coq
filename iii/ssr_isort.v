(**
プログラミング Coq 証明駆動開発入門(1)
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt8.html

をSSReflectに書き直した。
Permutation は SSReflect の相当の補題を使っているため、
証明の詳細は原著と異なることに注意してください。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(* Permutation, seq.v *)
Check perm_eq (1::2::3::nil) (2::1::3::nil).
Eval compute in perm_eq (1::2::3::nil) (2::1::3::nil). (* true *)
Eval compute in perm_eq nil nil.                       (* true *)

(* ソート処理の定義 *)
Fixpoint insert (a : nat)(l : seq nat) : seq nat :=
  match l with
  | nil => a :: nil
  | x :: xs => if leq a x then a :: l else x :: insert a xs
  end.

Fixpoint insertion_sort (l : seq nat) : seq nat :=
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

Theorem isort_permutation : forall (l : seq nat), perm_eq l (insertion_sort l).
Proof.
  elim=> [| a l H //=].
  - by [].
  - apply perm_eq_trans with (a :: insertion_sort l).
    + by rewrite perm_cons.
    + by apply insert_perm.
Qed.

(*
Require Import path.

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
*)

Inductive LocallySorted (T : eqType) (R : rel T) : seq T -> Prop :=
| LSorted_nil : LocallySorted R nil
| LSorted_cons1 : forall a : T, LocallySorted R (a :: nil)
| LSorted_consn : forall (a b : T) (l : seq T),
                    LocallySorted R (b :: l) ->
                    R a b -> LocallySorted R (a :: b :: l).

Check leq : nat -> nat -> bool.
Check leq : nat -> nat -> Prop.
Check leq : rel nat : Type.
Check le : nat -> nat -> Prop.
Fail Check le : nat -> nat -> bool.
Fail Check le : rel nat.                    (* rel : Type -> Type *)
Check LocallySorted leq (1::2::3::nil) : Prop.
Fail Check LocallySorted le (1::2::3::nil) : Prop.

Lemma leb_complete_conv : forall n m : nat, leq m n = false -> n < m.
Proof.
  move=> n m.
  move/negbT.
  by rewrite -ltnNge.
Qed.

Lemma insert_sorted : forall (a : nat) (l : seq nat),
                        LocallySorted leq l -> LocallySorted leq (insert a l).
Proof.
  move=> a.
  elim=> [H //= | a0 l IHl H //=].
  - by apply LSorted_cons1.
  - case Heqb : (leq a a0).                 (* remember *)
    + apply LSorted_consn.
      * by apply H.
      * by rewrite Heqb.
    + inversion H.
      * apply LSorted_consn.
        apply LSorted_cons1.
        apply ltnW.
        apply leb_complete_conv.
        by [].
      * subst.
        simpl.
        simpl in *.
        elim H' : (leq a b).
        - apply LSorted_consn.
          simpl in IHl.
          subst.
          rewrite H' in IHl.
          apply IHl.
          apply H2.
          apply ltnW.
          apply leb_complete_conv.
          by [].
        - apply LSorted_consn.
          rewrite H' in IHl.
          apply IHl.
          apply H2.
          apply H3.
Qed.

Theorem isort_sorted : forall (l : seq nat),
                         LocallySorted leq (insertion_sort l).
Proof.
  elim=> [| a l H //=].
  - by apply LSorted_nil.
  - by apply insert_sorted.
Qed.

(* END *)
