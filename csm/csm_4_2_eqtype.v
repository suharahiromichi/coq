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
opamでインストールしている場合は、ソースは、たとえば以下にあります。

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
# generic theory (ジェネリックな定理)

eqType に対して使える定理
 *)

(**
## eqP (= と == に間を変換する)
 *)
Check @eqP : forall (T : eqType) (x y : T), reflect (x = y) (x == y).

Lemma test : forall (x y : nat), x == y -> x + y == y + y.
Proof. move=> x y. by move=> /eqP ->. Qed.

Lemma test4 : forall (n m : nat), if n == m then true else true.
Proof. move=> n m.
       case: eqP => H.                      (* ifP でもよい。 *)
       (* H : n = m *)
       + done.
       + done.
Qed.

(**
## eq_refl と eq_sym (== の 反射性と対称性の補題)
 *)
Check eq_refl : forall (T : eqType) (x : T), x == x.
Check eq_sym  : forall (T : eqType) (x y : T), (x == y) = (y == x).

(**
## contraXX (== に関する対偶)

直観主義論理では、一般に対偶は成り立たないが、否定の側がboolなら成立する。
最後のふたつを覚えておけばよいかも。
 *)
Check contraTeq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x != y -> ~~ b) -> b -> x = y.
Check contraNeq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x != y -> b) -> ~~ b -> x = y.
Check contraFeq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x != y -> b) -> b = false -> x = y.
Check contraTneq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x = y -> ~~ b) -> b -> x != y.
Check contraNneq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x = y -> b) -> ~~ b -> x != y.
Check contraFneq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x = y -> b) -> b = false -> x != y.
Check contra_eqN : forall (T1 : eqType) (b : bool) (x y : T1),
    (b -> x != y) -> x = y -> ~~ b.
Check contra_eqF : forall (T1 : eqType) (b : bool) (x y : T1),
    (b -> x != y) -> x = y -> b = false.
Check contra_eqT : forall (T1 : eqType) (b : bool) (x y : T1),
    (~~ b -> x != y) -> x = y -> b.

Check contra_eq : forall (T1 T2 : eqType) (z1 z2 : T2) (x1 x2 : T1),
       (x1 != x2 -> z1 != z2) -> z1 = z2 -> x1 = x2.
Check contra_neq : forall (T1 T2 : eqType) (z1 z2 : T2) (x1 x2 : T1),
       (x1 = x2 -> z1 = z2) -> z1 != z2 -> x1 != x2.

(**
## eq_irrelevance

https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_axiom_free.v
 *)
Check eq_irrelevance  : forall (T : eqType) (x y : T) (e1 e2 : x = y), e1 = e2.


(**
# pcancel や cancel から eqType を定義する：

https://github.com/suharahiromichi/coq/blob/master/math-comp-book/suhara.ch7-windrose-2.v
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

(* balle2bool の単射性をつかってballe_eqTypeを定義する。 *)
Lemma inj_b2b : injective balle2bool.
Proof. by case; case. Qed.

Definition balle_eqMixin := InjEqMixin inj_b2b.
Canonical balle_eqType := EqType balle balle_eqMixin.

(* balle2bool と bool2balle が逆であることをつかってballe_eqTypeを定義する。 *)
Lemma can_b2b : cancel balle2bool bool2balle.
Proof. by case. Qed.

Definition balle_eqMixin' := CanEqMixin can_b2b.
Canonical balle_eqType' := EqType balle balle_eqMixin'.

(*
eqType の公理から balle_eqType を定義する。
*)

Definition balle_eqb (x y : balle) : bool :=
  match (x, y) with
  | (rouge, rouge) => true
  | (blanc, blanc) => true
  | _ => false
  end.

Lemma balle_eqb_spec x y : reflect (x = y) (balle_eqb x y).
Proof. apply: (iffP idP); by case: x; case y. Qed.

Definition balle_eqMixin'' := EqMixin balle_eqb_spec.
Canonical balle_eqType'' := EqType balle balle_eqMixin''.


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

(**
## その他

nat_eqType      nat.v
seq_eqType      seq.v
tree_eqType     choice.v
ordinal_eqType  fintype.v
*)


(* END *)
