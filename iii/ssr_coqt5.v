(**
プログラミング Coq --- 使えるタクティク集

http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt5.html
をSSReflectに書き直した。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Goal forall (P Q R S : Prop), (S /\ P) /\ (Q /\ R) -> (P /\ S) /\ (R /\ Q).
Proof.
  move=> P Q R S.
  elim.
  have H1 : forall (X Y : Prop), X /\ Y -> Y /\ X => H H0.
    by elim.
  split.
  - by apply: (H1 S P H).
  - by apply: (H1 Q R H0).
Qed.


Theorem app_eq_nil :
  forall (A : Type) (l l' : seq A), l ++ l' = nil -> l = nil /\ l' = nil.
Proof.
  move=> A l l' H.
  split.
  - by elim: l H.
  - elim: l' H.
    + by [].
    + by elim: l.
Qed.

Goal forall (A : Type) (a : A), nil <> a :: nil.
Proof.
  by [].
Qed.

Goal forall (n m : nat) (f : nat -> nat),
       f n = n -> S (f (f n)) = S m -> n = m.
Proof.
  congruence.
Qed.

Goal forall (A : Type) (x y : A),
       x :: y :: nil <> x :: nil.
Proof.
  congruence.
Qed.

Goal forall (P Q : nat -> Prop) (a : nat), P (a * 2) \/ Q (a * 2).
Proof.
  move=> P Q a.
  rewrite (_: (Q (a * 2)) = (Q (2 * a))).
  (* replace (Q (a * 2)) with (Q (2 * a)). *)
  Admitted.                                 (* OK *)

Goal forall (P : nat -> nat -> Prop) (a b c d : nat),
       P a d -> a = b -> c = d -> P b c.
Proof.
  move=> P a b c d H H0 H1.
  subst.
  by [].
Qed.

Fixpoint removelast (A : Type) (l : seq A) : seq A :=
  match l with
    | nil => nil
    | a :: nil => nil
    | a :: l => a :: removelast l
  end.

Lemma removelast_cons : forall (A : Type) (a : A) (l : list A), l <> nil ->
  removelast (a :: l) = a :: removelast l.
Proof.
  move=> A a.
  by elim=> [//= | a' l] => H0 H1.
Qed.

Lemma app_is_nil (A : Type) (l l' : seq A) : l ++ l' = [::] -> l' = [::].
Proof.
  by elim: l.
Qed.
(*
  elim: l => [//= | a l H H0].
  inversion H0.
*)

Lemma removelast_app : forall (A : Type) (l l' : seq A),
                         l' <> nil -> removelast (l ++ l') = l ++ removelast l'.
Proof.
  move=> A l l' H.
  elim: l => [//= | a l IHl].
  rewrite 2!cat_cons.
  rewrite removelast_cons.
  - by rewrite IHl.
  - rewrite /not => Hc.
    apply H.
    eapply app_is_nil.
    eapply Hc.
Qed.

Inductive InList (A : Type) (a : A) : list A -> Prop :=
| headIL : forall xs, InList a (a :: xs)
| consIL : forall x xs, InList a xs -> InList a (x :: xs).

Goal forall (A : Type)(l : seq A) (a a' : A),
       InList a (a' :: l) -> a = a' \/ InList a l.
Proof.
  move=> A l a a' H.
  by inversion H; [left | right].
Qed.
  
(* END *)
