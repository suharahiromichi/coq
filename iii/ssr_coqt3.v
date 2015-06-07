(**
プログラミング Coq --- リストを扱う

http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt3.html
をSSReflectに書き直した。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Theorem app_assoc : forall (A : Type) (l1 l2 l3 : seq A),
                      l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  move=> A.
  elim=> [// | a l l1 l2 l3 /=].
    by congr (a :: _).
Qed.

Fixpoint rev (A : Type)(l : list A) : list A :=
  match l with
  | nil => nil
  | x :: xs => rev xs ++ (x :: nil)
  end.

Theorem rev_app_distr : forall (A : Type) (l1 l2 : seq A),
                          rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  move=> A.
  elim=> [/= l2 | a l IHl l2 /=].
  + by rewrite cats0.
  + by rewrite catA; congr (_ ++ _).
Qed.


(* 前回の答え。 *)

Theorem problem2 : forall (P Q R : Prop),
                     (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move=> P Q R H H0 H1.
  by apply/H0/H/H1.
Qed.

Theorem problem3 : forall (P : Prop), ~ (P /\ ~ P).
Proof.
  rewrite /not => P.
  case=> H H0.
  by apply/H0/H.
Qed.

Theorem problem4 : forall (P Q : Prop),
                     ~ P \/ ~ Q -> ~ (P /\ Q).
Proof.
  rewrite /not => P Q H.
  case=> H0 H1.
  by case H => H2.
Qed.

Theorem problem5 : forall (P : Prop),
                     (forall (P : Prop), ~ ~ P -> P) -> P \/ ~ P.
Proof.
  rewrite /not => P H.
  apply: H => H0.
  apply: (H0).                              (* H0 を前提に残す。 *)
  right=> H1.
  apply: H0.
  by left.
Qed.

(* END *)
