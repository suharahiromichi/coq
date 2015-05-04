(**
「同値関係の保存」をSSReflectでやってみる。
Proper ==> は、SSReflect とは同居できないようだ。

@suharahiromichi
2015_05_03
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*
たぶん、SSReflectとは同居できない。
Require Import Basics Tactics Coq.Setoids.Setoid Morphisms.
*)
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Definition list := seq nat.

(* ****************************** *)
(* 同値関係                        *)
(* ****************************** *)
Definition list_equiv : list -> list -> bool :=
  fun r r' => sumn r == sumn r'.
Infix "=s=" := list_equiv (at level 70) : type_scope.

Goal 1::2::3::nil =s= 6::nil.
Proof.
  by [].
Qed.

Lemma list_equiv_refl : reflexive list_equiv.
Proof.
  rewrite /reflexive /list_equiv.
  by [].
Qed.

Lemma list_equiv_sym : symmetric list_equiv.
Proof.
  rewrite /symmetric /list_equiv.
  by [].
Qed.

Lemma list_equiv_trans : transitive list_equiv.
Proof.
  rewrite /transitive /list_equiv.
  move=> y x z.
  move/eqP => H1.
  move/eqP => H2.
  apply/eqP.
  by rewrite H1 H2.
Qed.

(* ****************************** *)
(* cons n に対してプロパーである。 *)
(* ****************************** *)
(*  Proper (list_equiv ==> list_equiv) (cons n) . *)
Lemma cons_list_Proper (n : nat) :
  forall r r', r =s= r' -> n :: r =s= n :: r'.
Proof.
  intros r r'.
  rewrite /list_equiv.
  move/eqP => H.
  apply/eqP => /=.
  by rewrite H.
Qed.

Goal forall r r' : list,
       r =s= r' -> 4 :: r =s= 4 :: r'.
Proof.
  move=> r r' H.
  apply cons_list_Proper.
  by rewrite H.
Qed.

(* ****************************** *)
(* append に対してプロパーである。 *)
(* ****************************** *)
(* Proper (route_equiv ==> route_equiv ==> route_equiv) append *)
Lemma append_route_Proper (r r' r'' r''' : list) :
    r =s= r'' -> r' =s= r''' -> r ++ r' =s= r'' ++ r'''.
Proof.
  move/eqP => H1.
  move/eqP => H2.
  apply/eqP.
  do 2 rewrite sumn_cat.
  by rewrite H1 H2.
Qed.

Goal forall r r' : list,
       r =s= r' -> 1::2::nil ++ r =s= 1::2::nil ++ r'.
Proof.
  move=> r r' H.
  apply append_route_Proper.
  - by [].
  - by [].
Qed.

Goal forall r r' : list,
       r =s= r' -> r ++ 1::2::nil =s= r' ++ 1::2::nil.
Proof.
  move=> r r' H.
  apply append_route_Proper.
  - by [].
  - by [].
Qed.

Goal forall r r' : list,
       r =s= r' ->
       1::nil ++ r ++ 2::3::nil =s= 1::nil ++ r' ++ 2::3::nil.
Proof.
  move=> r r' H.
  apply append_route_Proper.
  - by [].
  - apply append_route_Proper.
    + by [].
    + by [].
Qed.

(* END *)
