(**
An introduction to small scale reflection in Coq

6. Finite objects in SSReflect

http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset.

(* Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
*)

(**
6.1 Finite types
6.1.1 Finite types constructions
*)

Lemma bool_enumP : Finite.axiom [:: false; true].
(* テキストは [:: true, false] だが、変えてみた。 *)
Proof.
    by case.
Qed.
Definition bool_finMixin :=
  FinMixin bool_enumP.
Canonical Structure bool_finType :=         (* finType の定義 *)
  FinType bool bool_finMixin.

Print Finite.axiom.
(**
Finite.axiom (T : eqType) (e : seq e) :=
forall x, count (@pred1 T x) e = 1.

T型を要素とする配列eは、Tの任意の要素が1つだけある。
つまり、T型の要素を列挙した配列。
*)

(**
Exercise 6.1.1 finType on the unit type
*)
Lemma unit_enumP : Finite.axiom [:: tt].
Proof.
    by [].
Qed.
Definition unit_finMixin :=
  FinMixin unit_enumP.
Canonical Structure unit_finType :=         (* finType の定義 *)
  FinType unit unit_finMixin.

(**
Exercise 6.1.2 opt.
*)

Definition tuto_option_enum (T : finType) :=
  None :: [seq Some i | i <- Finite.enum T].
(* テキストの定義は、 None :: map some (Finite.enum T). だが *)

Lemma tuto_option_enumP : forall T : finType,
                       Finite.axiom (tuto_option_enum T).
Proof.
  move=> T.
  rewrite /Finite.axiom => x.
  case H : x.                               (* by x. *)
  - rewrite /= count_map /=.                (* x = Some a *)
            nat_norm.
    rewrite enumP.
      by [].
  - rewrite /= count_map /=.                (* x = None *)
            nat_congr.
    rewrite count_pred0.
    by [].
Qed.
(* rewrite はまとめて、(count_pred0, enumP) と書ける。 *)

Definition tuto_option_finMixin (T : finType) :=
  FinMixin (tuto_option_enumP T).

Canonical Structure tuto_option_finType (T : finType) :=
  FinType (option T) (tuto_option_finMixin T).

(* END *)
