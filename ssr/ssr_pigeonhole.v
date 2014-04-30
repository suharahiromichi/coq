(**
SSReflectによる鳩の巣定理の証明
======
@suharahiromichi

プログラミング Coq 自然数を扱う
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt4.html

鳩の巣原理の証明をSSReflectに移してみました。
証明の内容はまったく同じなので、比べるとおもしろいとおもいます。
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
  elim.
  (* xs = [] の場合 *)
    by [].
  (* xs = x :: xs' の場合 *)
  elim.
    (* a = 0 の場合 *)
    move=> xs IHxs H; apply lt_Snm_nm, IHxs in H.
    by elim: H => x; exists x; constructor.

  elim.
    (* a = 1 の場合 *)
    move=> _ xs IHxs H; apply lt_S_n, IHxs in H.
    by elim: H => x; exists x; constructor.

  (* a >= 2 の場合 *)
  move=> a.
  by exists a; constructor.
Qed.

(**
注意：「ソフトウェアの基礎」の練習問題とは、異なるので注意してください。

http://proofcafe.org/sf/Logic_J.
 *)

(* $Id: ssr_pigeonhole.v,v 1.20 2014/04/30 04:14:36 suhara Exp suhara $ *)
