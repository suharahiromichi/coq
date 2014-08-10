(**
An introduction to small scale reflection in Coq

5. Type inference using canonical structures

http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset.

Set Implicit Arguments.
(* この宣言は必須である。これによって省かれた項はコメントしてある。 *)
Unset Strict Implicit.
Import Prenex Implicits.

(**
5.1 Canonical Structures
*)

Record zmodule_mixin_of (T : Type) : Type :=
  ZmoduleMixin {
      zero : T;
      opp : T -> T;
      add : T -> T -> T;
      addA : associative add;
      addC : commutative add;
      addm0 : left_id zero add;
      add0m : left_inverse zero opp add
    }.

Record zmodule : Type :=
  Zmodule {
      carrier :> Type;
      spec : zmodule_mixin_of carrier
    }.
(** bool_zodule は少し後ろにずらした。 *)

Definition zmadd (Z : zmodule) := add (spec Z).
(* add の forall T の T （つまり、 zmodule_mixin_of (T : Type) の T)
 が省かれている。zmaddACの証明も同様。 *)

Notation "x \+ y" := (zmadd x y) (at level 50, left associativity).
(* zmadd の Zが省かれている。 *)

(** Excercise 5.1.1 *)
Lemma zmaddAC : forall (m : zmodule)(x y z : m),
                  x \+ y \+ z = x \+ z \+ y.
Proof.
  move=> m x y z.
  rewrite /zmadd.
  rewrite -[add (spec m) (add (spec m) x y) z]addA.
  rewrite [add (spec m) y z]addC.
  rewrite [add (spec m) x (add (spec m) z y)]addA.
  by [].
Qed.

(** bool_zodule *)

Definition bool_zmoduleMixin :=
  ZmoduleMixin
    (* 最初の4引数が省かれている。 *)
    (* Type:=bool zero:=false opp:=(@id bool) add:=addb *)
    addbA addbC addFb addbb.

Definition bool_zmodule := Zmodule (* bool *) bool_zmoduleMixin.
(* Zmodule の bool が省かれている。  *)
Variable b : bool_zmodule.

Canonical Structure bool_zmodule.           (* 以下が有効になる。 *)
Check false \+ true.                        (* bool_zmodule *)
Eval compute in false \+ true.              (* true *)

Goal forall x y z : bool, x (+) y (+) z = x (+) z (+) y.
Proof.
  Locate "(+)".                             (* addb *)
  apply zmaddAC.
Qed.

(* END *)
