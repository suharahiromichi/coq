(** An Ssreflect Tutorial *)

(** http://hal.archives-ouvertes.fr/docs/00/40/77/78/PDF/RT-367.pdf  *)

Require Import ssreflect ssrbool eqtype ssrnat.

(** 2.3 Two so-called paradoxes *)

Section R_sym_trans.
Variables (D : Type) (R : D -> D -> Prop).

Hypothesis R_sym : forall x y, R x y -> R y x.
Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

(**
対称律と遷移律だけでは、反射律は証明できない、ということ。
*)
Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
Proof.
  move=> x [y Rxy].
    by apply: R_trans _ (R_sym _ y _).
Qed.

Lemma refl_if' : forall x : D, (exists y, R x y) -> R x x.
Proof.
  move=> x.
  case=> [y Rxy].
  move: (R_sym x y Rxy).
  move: Rxy.
  move: R_trans.
  apply.
Qed.
End R_sym_trans.

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

Lemma drinker' : exists x, (P x -> forall y, P y).
Proof.
  move: (EM (exists y, ~P y)).
  case;
    [move=> [y notPy] | move=> nonotPy].
    (* 前提が、~ P y のとき *)
    by exists y.
  (* 前提が、~ (exists y, ~ P y) のとき *)
  exists d => HPd y.
  (* 排中律 (P y \/ ~ P y) *)
  move: (EM (P y)).
  (* \/の左右で場合分けする。 左が直ちにとける。 *)
  case=> // notPy.  (* 実際は、case; [move=> // | move=> notPy] *)
  (* ~ (exists y, ~ P y) で場合分けする。 *)
  by case: nonotPy; exists y.
Qed.
End Smullyan_drinker.

(* END *)
