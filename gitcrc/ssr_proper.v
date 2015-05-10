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

Definition lsum := seq nat.

(* ****************************** *)
(* 同値関係                        *)
(* ****************************** *)
Definition lsum_equiv : lsum -> lsum -> bool :=
  fun r r' => sumn r == sumn r'.
Infix "=s=" := lsum_equiv (at level 70) : type_scope.

Goal 1::2::3::nil =s= 6::nil.
Proof.
  by [].
Qed.

Lemma lsum_equiv_refl : reflexive lsum_equiv.
Proof.
  rewrite /reflexive /lsum_equiv.
  by [].
Qed.

Lemma lsum_equiv_sym : symmetric lsum_equiv.
Proof.
  rewrite /symmetric /lsum_equiv.
  by [].
Qed.

Lemma lsum_equiv_trans : transitive lsum_equiv.
Proof.
  rewrite /transitive /lsum_equiv.
  move=> y x z.
  move/eqP => H1.
  move/eqP => H2.
  apply/eqP.
  by rewrite H1 H2.
Qed.

(* ****************************** *)
(* cons n に対してプロパーである。 *)
(* ****************************** *)
(*  Proper (lsum_equiv ==> lsum_equiv) (cons n) . *)
Lemma cons_lsum_Proper (n : nat) :
  forall r r', r =s= r' -> n :: r =s= n :: r'.
Proof.
  intros r r'.
  rewrite /lsum_equiv.
  move/eqP => H.
  apply/eqP => /=.
  by rewrite H.
Qed.

Goal forall r r' : lsum,
       r =s= r' -> 4 :: r =s= 4 :: r'.
Proof.
  move=> r r' H.
  apply cons_lsum_Proper.
  by rewrite H.
Qed.

(* ****************************** *)
(* append に対してプロパーである。 *)
(* ****************************** *)
(* Proper (route_equiv ==> route_equiv ==> route_equiv) append *)
Lemma append_route_Proper (r r' r'' r''' : lsum) :
    r =s= r'' -> r' =s= r''' -> r ++ r' =s= r'' ++ r'''.
Proof.
  move/eqP => H1.
  move/eqP => H2.
  apply/eqP.
  do 2 rewrite sumn_cat.
  by rewrite H1 H2.
Qed.

Goal forall r r' : lsum,
       r =s= r' -> 1::2::nil ++ r =s= 1::2::nil ++ r'.
Proof.
  move=> r r' H.
  apply append_route_Proper.
  - by [].
  - by [].
Qed.

Goal forall r r' : lsum,
       r =s= r' -> r ++ 1::2::nil =s= r' ++ 1::2::nil.
Proof.
  move=> r r' H.
  apply append_route_Proper.
  - by [].
  - by [].
Qed.

Goal forall r r' : lsum,
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

(* ******************************** *)
(* ********EqMixin***************** *)
(* ********説明のための例*********** *)
(* ******************************** *)

(* SSReflect (EqType) でできること。 *)
(* jssst31/ssr_jsst2014_eqtype_example.v *)
Lemma lsum_equivP : Equality.axiom lsum_equiv.
Proof.
  move=> r r'.
  rewrite /lsum_equiv.
  apply: (iffP idP).
(* これは成立しないが、説明のために仮におく。 *)
  - admit.
  - move=> <-.
    by apply: lsum_equiv_refl.
Qed.

Compute 1::2::3::nil == 6::nil :> seq nat.  (* false *)
Compute 1::2::3::nil == 6::nil :> lsum.     (* false *)

Canonical lsum_eqMixin := EqMixin lsum_equivP.
Canonical lsum_eqType := EqType lsum lsum_eqMixin.
(* Canonical lsum_eqType := Eval hnf in EqType lsum lsum_eqMixin. *)
Print Canonical Projections.
(*
lsum_equiv <- Equality.op ( lsum_eqMixin )
lsum <- Equality.sort ( lsum_eqType )
が追加になる。
*)

Compute 1::2::3::nil == 6::nil :> seq nat.  (* false *)
Compute 1::2::3::nil == 6::nil :> lsum.     (* true *)
(* lsum 型の世界で、== が使えるようになる。 *)

(* ******** *)
Lemma lsum_irrelevance (x y : lsum) (E E' : x = y) : E = E'.
Proof. by apply: eq_irrelevance. Qed.
(* ******* *)

Goal 1::2::3::nil == 6::nil :> lsum.
Proof.
  by [].
Qed.

(** 証明 *)
Goal forall r r' : lsum, r == r' <-> r = r'.
Proof.
  move=> r r'.
  by split; move/lsum_equivP.
Qed.

(** リフレクションと書き換えができる。  *)
Goal forall r r' l : nat, r == r' -> r' == l -> r == l.
Proof.
  move=> r r' l Hrr' Hr'l.
  apply/eqP.                                (* r = l *)
  Undo 1.
  rewrite (eqP Hrr').                       (* r' == l *)
  by [].
Qed.

(* END *)

(* SSReflect の部分の参考：
http://d.hatena.ne.jp/kikx/20111213 *)
