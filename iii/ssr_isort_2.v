(**
プログラミング Coq 証明駆動開発入門(1)
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt8.html

をSSReflectに書き直した。
Permutation は SSReflect の相当の補題を使っているため、
証明の詳細は原著と異なることに注意してください。
*)

(* ************************************************** *)
(* nat と ≦ より一般的な、eqType と R で証明を試みる。 *)
(* ************************************************** *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Section isort.
  Variables T : eqType.
  Variables R R' : rel T.

  (* Permutation, seq.v *)
  Check perm_eq (1::2::3::nil) (2::1::3::nil).
  Eval compute in perm_eq (1::2::3::nil) (2::1::3::nil). (* true *)
  Eval compute in perm_eq nil nil.                       (* true *)

  (* ソート処理の定義 *)
  Fixpoint insert (a : T) (l : seq T) : seq T :=
    match l with
      | nil => a :: nil
      | x :: xs => if R a x then a :: l else x :: insert a xs
    end.

  Fixpoint insertion_sort (l : seq T) : seq T :=
    match l with
      | nil => nil
      | x :: xs => insert x (insertion_sort xs)
    end.

  (* 証明 *)
  Lemma perm_iff : forall (m n : seq T),
                   (forall l, perm_eq m l = perm_eq n l) <-> perm_eq m n.
  Proof.
    move=> m n.
    split=> H.
    - by rewrite H.
    - by apply/perm_eqlP.
  Qed.

  Lemma perm_swap : forall (l l' : seq T) (x a : T),
                      perm_eq [:: x, a & l] l' = perm_eq [:: a, x & l] l'.
  Proof.
    move=> l l' x a.
    apply perm_iff => //.
    rewrite -[[:: x, a & l]]cat1s -[[:: a & l]]cat1s.
    apply/perm_eqlP.
      by apply (perm_catCA [:: x] [:: a] l).
  Qed.

  Lemma insert_perm : forall (l : seq T) (x : T),
                        perm_eq (x::l) (insert x l).
  Proof.
    elim=> [_ // | a l H x //=].
    case: (R x a) => [//= |].
    apply perm_iff => // l'.
    rewrite perm_swap => //.
    apply perm_iff => //.
    by rewrite perm_cons.
  Qed.

  Theorem isort_permutation : forall (l : seq T),
                                perm_eq l (insertion_sort l).
  Proof.
    elim=> [// | a l H //=].
    apply perm_eq_trans with (a :: insertion_sort l).
    + by rewrite perm_cons.
    + by apply insert_perm.
  Qed.

  Inductive LocallySorted : seq T -> Prop :=
  | LSorted_nil : LocallySorted nil
  | LSorted_cons1 : forall a : T, LocallySorted (a :: nil)
  | LSorted_consn : forall (a b : T) (l : seq T),
                      LocallySorted (b :: l) ->
                      R a b -> LocallySorted (a :: b :: l).
  
  Lemma complete_conv : forall n m : T, ~ R m n -> R n m.
  Proof.
    admit.
  Qed.
  
  Lemma insert_sorted : forall (a : T) (l : seq T),
                          LocallySorted l -> LocallySorted (insert a l).
  Proof.
    move=> a.
    elim=> [H //= | a0 l IHl H //=].
    - by apply LSorted_cons1.
    - case Heqb : (R a a0).                 (* remember *)
      + apply LSorted_consn.
        * by apply H.
        * by rewrite Heqb.
      + inversion H.
        * apply LSorted_consn.
          apply LSorted_cons1.
          by move: Heqb => /negP /complete_conv.
        * subst; simpl; simpl in *.
          elim H' : (R a b).
          - apply LSorted_consn.
            + by rewrite H' in IHl; apply IHl. (* apply H2. *)
            + by move: Heqb => /negP /complete_conv.
          - apply LSorted_consn.
            + by rewrite H' in IHl; apply IHl. (* apply H2. *)
            + by [].                           (* apply H3. *)
  Qed.
  
  Theorem isort_sorted : forall (l : seq T),
                           LocallySorted (insertion_sort l).
  Proof.
    elim=> [| a l H //=].
    - by apply LSorted_nil.
    - by apply insert_sorted.
  Qed.

End isort.

Eval compute in insert leq 1 nil.                      (* [:: 1] *)
Eval compute in insert leq 5 [:: 1; 4; 2; 9; 3].       (* [:: 1; 4; 2; 5; 9; 3] *)
Eval compute in insertion_sort leq [:: 2; 4; 1; 5; 3]. (* [:: 1; 2; 3; 4; 5] *)

Check leq : nat -> nat -> bool.
Check leq : nat -> nat -> Prop.
Check leq : rel nat : Type.
Check le : nat -> nat -> Prop.
Fail Check le : nat -> nat -> bool.
Fail Check le : rel nat.                    (* rel : Type -> Type *)
Check LocallySorted leq (1::2::3::nil) : Prop.
Fail Check LocallySorted le (1::2::3::nil) : Prop.

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

(* END *)
