(**
サブタイプ sub-type kit の使用例

2023_09_23 @suharahiromichi

 *)

From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From common Require Import ssrstring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# サブタイプ (subType)

MathCompの型クラスである。eqTypeのたぐいと思えばよい。サブタイプを定義するための道具は、
サブタイプキットと呼ばれる場合もあり、eqtype.v で定義されている。
*)

Definition EList := [:: "up"; "off"; "down"].

(* Inductive updown : predArgType := UpDown m of m \in EList. *)
Inductive updown : predArgType :=
| UpDown m (_ : m \in EList).

(* Coercion string_of_updown i := let: @UpDown m _ := i in m. *)
Coercion string_of_updown i :=
  match i with
  | @UpDown m _ => m
  end.

Check @UpDown "up" (isT : "up" \in EList).
Check UpDown (isT : "up" \in EList).

Definition up   := UpDown (isT : "up"   \in EList).
Definition down := UpDown (isT : "down" \in EList).
Definition off  := UpDown (isT : "off"  \in EList).

Compute string_of_updown up.                (* "up" *)
Compute string_of_updown down.              (* "down" *)
Compute string_of_updown off.               (* "off" *)

(**
val と \val は同じ。eqtype.v で定義されている。
the generic injection from a subType S of T into T

eqType なら "==" が使えるように、（なにかの）サブタイプなら val や \val が使える。
ただし、自然数に対してeqn も使い続けられるように、nat_of_ord も使える。
*)
HB.instance Definition _ := [isSub for string_of_updown].

Compute \val up.                            (* "up" *)
Compute \val down.                          (* "down" *)
Compute \val off.                           (* "off" *)

Compute "up" \in EList.
Compute "above" \in EList.

(*
うまく計算できない。
*)
Compute insub "up".
Compute insub "above".

(*
参考

ここでは、特別に Equality (eqType) を定義しない。
*)
Compute up == up.            (* string へのコアーションで成り立つ。 *)


(**
MathComp のサブタイプの例

```
ssreflect/tuple.v:HB.instance Definition _ := [isSub for tval].
ssreflect/fintype.v:HB.instance Definition _ := [isSub of ordinal for nat_of_ord].
algebra/rat.v:Definition rat_isSub := Eval hnf in [isSub for valq].
algebra/poly.v:HB.instance Definition _ := [isSub for polyseq].

MathComp1 の [SubType for ...] だから、少し、わかりにくくなったかも。
```
*)

Check tval       : forall (n : nat) (T : Type), n.-tuple T -> seq T.
Check nat_of_ord : forall n : nat, 'I_n -> nat.
Check valq       : rat -> int * int.
Check @polyseq   : forall R : semiRingType, polynomial R -> seq R.

Check val : 3.-tuple nat -> seq nat.
Check val : 'I_3 -> nat.
Check val : rat -> int * int.
Check val : polynomial int -> seq int.

(**
サブタイプキットは、val の他に、insub や insubd を提供する。eqtype.v に説明がある。
 *)

(* END *)
