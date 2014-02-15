(**
プログラミング Coq 自然数を扱う
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt4.html

鳩の巣原理の証明をSSReflectに移した。証明の内容はまったく同じ。
@suharahiromichi
 *)
Require Import ssreflect ssrbool ssrnat seq.

Lemma lt_S_n : forall (n m : nat), S n < S m -> n < m.
Proof.
  by [].
Qed.

Lemma lt_Snm_nm : forall (n m : nat), S n < m -> n < m.
Proof.
  move=> n m.
  by apply (@ltn_trans n.+1 n m).
Qed.

Inductive InList (A : Type)(a : A) : list A -> Prop :=
| headIL : forall xs, InList A a (a::xs)                     (* 1 *)
| consIL : forall x xs, InList A a xs -> InList A a (x::xs). (* 2 *)

Theorem pigeonhole : forall (xs : list nat),
                       size xs < foldr plus 0 xs ->
                       exists x : nat, InList nat x.+2 xs.
Proof.
  move=> xs. elim: xs.
  (* xs = [] の場合 *)
    by [].
  (* xs = x :: xs' の場合 *)
    move=> /= a.
    elim: a.
      (* a = 0 の場合 *)
      move => xs IHxs H.
      apply lt_Snm_nm in H.
      apply IHxs in H.
      elim: H => x.
      exists x. by constructor.

    move=> /= a.
    elim: a.
      (* a = 1 の場合 *)
      move=> /= H1 xs IHxs H.
      apply lt_S_n in H.
      apply IHxs in H.
      elim: H => x.
      exists x. by constructor.

    move=> /= a.
      (* a >= 2 の場合 *)
      exists a. by constructor.      
Qed.

(* END *)
