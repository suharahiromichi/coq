(**
プログラミング Coq --- 証明ができない！ こんなとき

http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt6.html
をSSReflectに書き直した。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Inductive InList (A : Type) (a : A) : seq A -> Prop :=
  | headIL : forall xs, InList a (a::xs)   (* 1 *)
  | consIL : forall x xs, InList a xs -> InList a (x::xs).   (* 2 *)

Goal forall (A : Type) (a : A) (l : seq A),
       (forall (x y : A), x = y \/ x <> y) -> InList a l \/ ~ InList a l.
Proof.
  move=> A a l H.
  elim: l.
  - right=> H0.
      by inversion H0.
  - move=> a0 l IHl.
    elim: IHl => H1.
    + left.
        by apply consIL.
    + elim: (H a a0) => H2.
      * left.
        rewrite H2.
          by apply headIL.
      * right.
        move=> H3.
          by inversion H3.
Qed.

Theorem fold_symmetric :                    (* standard coq. *)
  forall (A:Type) (f:A -> A -> A),
    (forall x y z:A, f x (f y z) = f (f x y) z) ->
    (forall x y:A, f x y = f y x) ->
    forall (a0:A) (l:list A), foldl f a0 l = foldr f a0 l.
Proof.
  destruct l.
  - reflexivity.
  - simpl.
    generalize a, a0.
    induction l.
    + intros.
      simpl.
      now apply H0.
    + simpl.
      intros.
      rewrite H.
      replace (f (f a3 a2) a1) with (f a3 (f a2 a1)).
      * now apply IHl.
      * now apply H.
Qed.

Theorem fold_symmetric' :                   (* SSReflect *)
  forall (A : Type) (f : A -> A -> A),
    (forall x y z : A, f x (f y z) = f (f x y) z) -> (* 結合則 *)
    (forall x y : A, f x y = f y x) ->               (* 交換則 *)
    forall (a0 : A) (l : seq A), foldl f a0 l = foldr f a0 l.
Proof.
  move=> A f Hassoc Hcomm a0 l.
  elim: l => [//= | /= a l _].              (* 前提 : foldl f a0 l = foldr f a0 l を消す。 *)
  - elim: l a a0 => [a1 a2 /= | /= a1 l IHl a2 a3].
    + by apply: Hcomm.
    + rewrite Hassoc.
      rewrite (_ : f (f a3 a2) a1 = f a3 (f a2 a1)).
      (* replace (f (f a3 a2) a1) with (f a3 (f a2 a1)). *)
      * by apply: IHl.
      * by rewrite Hassoc.
Qed.

Theorem problem8 : forall (n : nat),
                     (exists m, n = 2 * m) \/ (exists m, n = 2 * m + 1).
Proof.
  elim=> [|n IHn].
  - left.
    by exists 0.
  - elim: IHn.
    + right.
      elim: H => x H.
      exists x.
      by rewrite H addnC.
    + elim=> x H.
      left.
      exists x.+1.
      rewrite addnC in H.
      by rewrite mulnSr addnC H.
Qed.

Theorem problem9 : forall (A : Type) (l m : seq A) (a : A),
                     InList a (l ++ m) -> InList a l \/ InList a m.
Proof.
  move=> A l m a.
  elim: l => [H| a0 l IHl H].
  - right.
    by apply H.
  - inversion H.
    + subst.
      left.
      by apply: headIL.
    + elim: (IHl H1).
      * left.
        by apply: consIL.
      * right.
        by apply H3.
Qed.

(* END *)
