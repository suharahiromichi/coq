(**
N-Queens

finTypeの使い方を確かめるために、8クィーン問題の盤面の記述を試みる。
実際には4×4盤面を扱う。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import fintype finfun finset fingroup perm.
(* perm は順列ではなく、置換のパッケージである。 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* 行または列をしめす、0〜3の値を 'I_4型で定義する。 *)
Definition p0 : 'I_4. Proof. have : 0 < 4 by []. apply Ordinal. Defined.
Definition p1 : 'I_4. Proof. have : 1 < 4 by []. apply Ordinal. Defined.
Definition p2 : 'I_4. Proof. have : 2 < 4 by []. apply Ordinal. Defined.
Definition p3 : 'I_4. Proof. have : 3 < 4 by []. apply Ordinal. Defined.

(* 同じ行(列)は「=」が成立する。 *)
Goal p1 = p1.
Proof.
    by [].
Qed.

(* 違う行(列)は「<>」が成立する。 *)
Goal p1 <> p2.
Proof.
  by [].
Qed.

(* 蛇足： set について *)
Compute [set p0; p1; p2; p3] \in {set 'I_4}.
Check [:: p0; p1; p2; p3] : seq 'I_4.

(* tpermの引数は置換後の値 *)
(*
盤面は、列に対して、駒のいる行を返す置換、として定義する。
4-Queensの場合の解は、列(0,1,2,3)に対して、行(1,3,0,2)の置換になっている。

 0 1 2 3   列
 1 3 0 2   行
|-|-|Q|-|
|Q|-|-|-|
|-|-|-|Q|
|-|Q|-|-|
*)

(* 上記の置換が次のように記述できる。置換なので'I_4 -> 'I_4の型である。 *)
Definition board1 : 'I_4 -> 'I_4 :=
  (tperm p2 p3) \o (tperm p0 p2) \o (tperm p0 p1).

(* tperm _ _ は、{perm T}型だが、コアーションが効いているのだ *)
Check (tperm p2 p3) : {perm 'I_4}.
Check (tperm p2 p3) : 'S_4.
(* Coercionが効いている。 *)
Check fun_of_perm (tperm p2 p3) : 'I_4 -> 'I_4.

(* tperm についての補題 *)
Check tpermL.                               (* (tperm x y) y = x *)
Check tpermR.                               (* (tperm x y) y = x *)
Check tpermD.                               (* (tperm x y) z = z *)

(* tpermの引数を置換後の値で書く場合 *)
(* 列(0,1,2,3)に対して、行(1,3,0,2)がえられることを確認する *)
(* tpermDを使う場所を間違えると解けなくなる。 *)
Goal board1 p0 = p1.
Proof.
  rewrite /board1 /=.
  rewrite ?tpermR ?tpermL.
  rewrite [(tperm _ _) p1]tpermD => //=.
  rewrite [(tperm _ _) p1]tpermD => //=.
Qed.

Goal board1 p1 = p3.
Proof.
  rewrite /board1 /=.
  rewrite ?tpermR ?tpermL.
  by [].
Qed.

Goal board1 p2 = p0.
Proof.
  rewrite /board1 /=.
  rewrite ?tpermR ?tpermL.
  rewrite [(tperm _ _) p2]tpermD => //=.
  rewrite ?tpermR ?tpermL.
  rewrite [(tperm _ _) p0]tpermD => //=.
Qed.

Goal board1 p3 = p2.
Proof.
  rewrite /board1 /=.
  rewrite ?tpermR ?tpermL.
  rewrite [(tperm _ _) p3]tpermD => //=.
  rewrite [(tperm _ _) p3]tpermD => //=.
  rewrite ?tpermR ?tpermL.
  by [].
Qed.


(* tpermの引数を置換前の値で書く場合 *)
(* 置換としてはおなじ。 *)
Definition board2 :=
  (tperm p0 p1) \o (tperm p1 p2) \o (tperm p1 p3).

Check tpermL.                               (* (tperm x y) y = x *)
Check tpermR.                               (* (tperm x y) y = x *)
Check tpermD.                               (* (tperm x y) z = z *)

Goal board2 p0 = p1.
Proof.
  rewrite /board2 /=.
  rewrite [(tperm _ _) p0]tpermD //=.
  rewrite [(tperm _ _) p0]tpermD //=.
  by rewrite ?tpermR ?tpermL.
Qed.

Goal board2 p1 = p3.
Proof.
  rewrite /board2 /=.
  rewrite ?tpermR ?tpermL.
  rewrite [(tperm _ _) p3]tpermD //=.
  rewrite [(tperm _ _) p3]tpermD //=.
Qed.

Goal board2 p2 = p0.
Proof.
  rewrite /board2 /=.
  rewrite [(tperm _ _) p2]tpermD //=.
  by rewrite ?tpermR ?tpermL.
Qed.

Goal board2 p3 = p2.
Proof.
  rewrite /board2 /=.
  rewrite ?tpermR ?tpermL.
  by rewrite [(tperm _ _) p2]tpermD //=.
Qed.

(* ふたつの盤面が同じであることを示す。 *)
Goal board1 =1 board2.
Proof.
  case.
  admit.
Qed.  

(* (p列, b p行)の駒と、(q列, b q行)の駒が、
筋にいるとき真となる命題を定義する。 *)
Definition attacked (b : 'I_4 -> 'I_4)  (p q : 'I_4) :=
    p = q \/
    b p = b q \/
    b p + p = b q + q \/
    b p + q = b q + q.

(* (p0, p1)の駒と、(p1, p3)の駒が、筋にないこと示す。 *)
Goal ~ attacked board1 p0 p1.
Proof.
  rewrite /attacked /board1.
  case; case; case => /= H.
  - by [].
  - rewrite ?tpermL ?tpermR in H.
    rewrite [(tperm _ _) p1]tpermD //= in H.
    rewrite [(tperm _ _) p1]tpermD //= in H.
    by rewrite ?tpermL ?tpermR in H.
  - rewrite ?tpermL ?tpermR in H.
    rewrite [(tperm _ _) p1]tpermD //= in H.
    rewrite [(tperm _ _) p1]tpermD //= in H.
    by rewrite ?tpermL ?tpermR in H.
  - rewrite ?tpermL ?tpermR in H.
    rewrite [(tperm _ _) p1]tpermD //= in H.
    rewrite [(tperm _ _) p1]tpermD //= in H.
    by rewrite ?tpermL ?tpermR in H.
Qed.

(* (p行, b p列)の駒と、(q行, b q列)の駒が、
筋にいるとき真となる命題を定義する。 bool版 *)
Definition attacked' (b : 'I_4 -> 'I_4)  (p q : 'I_4) : bool :=
    (p == q) ||
    (b p == b q) ||
    (b p + p == b q + q) ||
    (b p + q == b q + q).

Definition consistent (b : 'I_4 -> 'I_4) :=
  [forall p : 'I_4, forall q : 'I_4, ~~ attacked' b p q].

Goal consistent board1.
Proof.
  rewrite /consistent /attacked'.
  apply/forallP => p.
  Check negb_exists.
  rewrite -negb_exists.
  apply/negP=> H.
  move/existsP in H.
  case: H.
  move=> q.
  admit.
Qed.

(* END *)
