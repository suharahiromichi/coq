(** An Ssreflect Tutorial *)

(** http://hal.archives-ouvertes.fr/docs/00/40/77/78/PDF/RT-367.pdf  *)

Require Import ssreflect ssrbool eqtype ssrnat.

(** 2.3 Two so-called paradoxes *)

(**
その1. 対称律と遷移律だけでは、反射律は証明できない、ということ。
*)
Section R_sym_trans.
Variables (D : Type) (R : D -> D -> Prop).

Hypothesis R_sym : forall x y, R x y -> R y x.
Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
Proof.
  move=> x [y Rxy].
    by apply: R_trans _ (R_sym _ y _).
Qed.

Lemma refl_if' : forall x : D, (exists y, R x y) -> R x x.
Proof.
  move=> x.
  (* (exists y : D, R x y) -> R x x *)
  case.
  (* forall y : D, (R x y -> R x x) *)
  move=> y Rxy.
  (* R x x *)
  move: (R_sym x y Rxy).                    (* R y x *)
  move: Rxy.                                (* R x y *)
  move: (R_trans x y x).                    (* R x y -> R y x -> R x x *)
  apply.
Qed.
End R_sym_trans.

(**
その2. スマリヤン・ドリンカー
 *)
Section Smullyan_drinker.
Variables (D : Type) (P : D -> Prop).

Hypothesis (d : D) (EM : forall A, A \/ ~A). (* 排中律 *)

Lemma drinker : exists x, P x -> forall y, P y.
Proof.
  case: (EM (exists y, ~P y)) => [[y notPy] | nonotPy];
  first by exists y.
    exists d => _ y;
      case: (EM (P y)) => // notPy.
      by case: nonotPy; exists y.
Qed.

(* 分解した書き方 *)
Lemma drinker' : exists x, (P x -> forall y, P y).
Proof.
  Check (EM (exists y, ~P y)).
  (* (exists y : D, ~ P y) \/ ~ (exists y : D, ~ P y) *)
  move: (EM (exists y, ~P y)).
  case.
  (* (exists y : D, ~ P y) -> exists x : D, (P x -> forall y : D, P y) *)
    move=> [y notPy].
    exists y.
    done.
  (* (**) ~ (exists y : D, ~ P y) -> exists x : D, P x -> forall y : D, P y *)
  move=> nonotPy.
  exists d => HPd y.
  (* P y *)

  Check (EM (P y)).
  (* 排中律 (P y \/ ~ P y) *)
  move: (EM (P y)).
  (* P y \/ ~ P y -> P y *)
  case.
  (*P y -> P y *)
    move=> //.
  (* ~ P y -> P y *)
  move=> notPy.
  move: nonotPy. 
  (* ~ (exists z : D, ~ P z) -> P y *)
  case.
  (* exists z : D, ~ P z *)
  exists y.
  (* ~ P y *)
  done.
Qed.

(**
最初の排中律を左側の場合を使ったゴールが、パラドックスの本質なのだが、簡単に解けてしまう。
排中律の右側の場合を使ったゴール (**) は、
~ (exists y : D, ~ P y) -> exists x : D, P x -> forall y : D, P y

スタックの先頭をドモルガンの定理で書き換えられるなら簡単にとけてしまう。
(forall y : D, P y) -> exists x : D, P x -> forall y : D, P y

そこで、ドモルガンの定理だけを証明する部分を取り出してみる。
ここにも、排中律が必要である。
*)

Lemma deMorgan : ~ (exists y : D, ~ P y) -> forall y : D, P y.
Proof.
  move=> nonotPy y.
  move: (EM (P y)).
  case.
    by [].
  move=> notPy.
  move: nonotPy.
  case.
  exists y.
  by [].
Qed.

Lemma drinker'' : exists x, (P x -> forall y, P y).
Proof.
  Check (EM (exists y, ~P y)).
  (* (exists y : D, ~ P y) \/ ~ (exists y : D, ~ P y) *)
  move: (EM (exists y, ~P y)).
  case.
  (* (exists y : D, ~ P y) -> exists x : D, (P x -> forall y : D, P y) *)
  (* 誰も飲んでいないなら、（誰かが飲んでいれば）、皆が飲んでいる、は成立する。 *)
    move=> [y notPy].
    exists y.
    done.
  (* ~ (exists y : D, ~ P y) -> exists x : D, (P x -> forall y : D, P y) *)
  (* (forall y : D, P y) -> exists x : D, P x -> forall y : D, P y *)
  (* 皆が飲んでいるなら、（誰かが飲んでいれば）、皆が飲んでいる、は成立する。 *)
  move=> nonotPy.
  exists d => HPd y.
  apply: deMorgan.
  apply: nonotPy.
Qed.

End Smullyan_drinker.

(* END *)
