Require Import ssreflect.

(**
# 第4回 Curry-Howard対応/Churchエンコーディング

http://qnighy.github.io/coqex2014/ex4.html

## 課題19 (種別:B / 締め切り : 2014/05/11)

帰納型を使わずにイコールを定義し、それが標準ライブラリのeqの定義と同値であることを証明せよ。
*)

Parameter A : Set.

(**
帰納型を使わずにイコール(Eq)を定義する。
 *)
Definition Eq : A -> A -> Prop :=
  fun (a b : A) =>
    forall (P : A -> Prop), P a -> P b.

(**
Eqか標準ライブラリのeq(=)の定義と同値であることを証明する。
*)
Lemma Eq_eq : forall x y, Eq x y <-> x = y.
Proof.
  move=> x y.
  split.
  (* Eq x y -> x = y *)
    by apply.
  (* x = y -> Eq x y *)
  move=> H P.
  by rewrite H.
Qed.

(* END *)
