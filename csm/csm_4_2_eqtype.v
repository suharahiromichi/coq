(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.2 eqtype.v --- eqType型のためのライブラリ

======

2018_11_17 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ssrbool.v のソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/eqtype.v
*)

(**
# eqType 型クラス （テンプレート）

eqType型クラスのインスタンス型 string_eqType を作る：
 *)

(*
(* String.v での定義を使う。 *)
Require Import String.
Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.
 *)

(* csm_4_1_ssrbool.v での定義を使う。 *)
Require Import String csm_4_1_ssrbool.
Definition string_eqMixin := @EqMixin string string_eqb string_eqP.
Canonical string_eqType := EqType string string_eqMixin.

(**
## eqP と eqE
 *)

(**
## eq_refl と eq_sym
 *)

(**
## contraXX
 *)

(**
## eq_irrelevance
 *)

(**
# pcancel や cancel から eqType を定義する：

coq/math-comp-book/suhara.ch7-windrose-2.v も参照のこと。
*)

Inductive balle :=
| rouge  (* red ball, la balle rouge, 紅玉 *)
| blanc. (* white ball, la balle blanc, 白玉 *)

Definition balle2bool (b : balle) : bool :=
  match b with
  | rouge => true
  | blanc => false
  end.

Definition bool2balle (b : bool) : balle :=
  match b with
  | true => rouge
  | false => blanc
  end.

(* balle2bool の単射性をつかってeqTypeを定義する。 *)
Lemma inj_b2b : injective balle2bool.
Proof. by case; case. Qed.

Definition balle_eqMixin := InjEqMixin inj_b2b.
Canonical balle_eqType := EqType balle balle_eqMixin.

(* balle2bool と bool2balle が逆であることをつかってeqTypeを定義する。 *)
Lemma can_b2b : cancel balle2bool bool2balle.
Proof. by case. Qed.

Definition balle_eqMixin' := CanEqMixin can_b2b.
Canonical balle_eqType' := EqType balle balle_eqMixin'.


(**
# eqType型のインスタンス
 *)

(**
## unit_eqType
 *)

(**
## bool_eqType
 *)

(**
## unit_eqType
 *)

(**
## prod_eqType (直積型)
 *)

(**
## option_eqType
 *)

(**
## tag_eqType
 *)

(**
## sum_eqType
 *)


(* END *)
