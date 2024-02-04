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

string 型のサブタイプとして、up, down, off だけからなる updown型を定義してみる。
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
## val の使い方 - サブタイプからもとの型の値を返す。

val と \val は同じ。eqtype.v で定義されている。
the generic injection from a subType S of T into T

eqType なら "==" が使えるように、（なにかの）サブタイプなら val や \val が使える。
ただし、自然数に対してeqn も使い続けられるように、nat_of_ord も使える。
*)
Fail Check val : updown -> string.
HB.instance Definition _ := [isSub for string_of_updown].
Check val : updown -> string.

Compute \val up.                            (* "up" *)
Compute \val down.                          (* "down" *)
Compute \val off.                           (* "off" *)

Compute "up" \in EList.
Compute "above" \in EList.

(*
## insubd の使い方 - もとの型からサブタイプ型の値を作る。

``insubd u0 x : sT`` のとき x が sT に変換できるなら変換する。さもなければ u0 を返す。
 *)
Check insubd off : string -> updown.
Check @insubd string (fun s => s \in EList) updown off : string -> updown.

Check insubd off "up" = up. (* 右辺が up なので updown とわかる。*)
(* 以下の書き方もある。 *)
Check (insubd off "up" : updown) = up.
Check insubd off "up" = up :> updown.
(* 関数にして、値の型を明確にしておくことがふつうである。 *)
Definition inupdownd (s : string) : updown := insubd off s.

Goal inupdownd "up" = up.
Proof.
  rewrite /inupdownd.
  Check insubd off "up" = up.               (* updown 型 *)
  apply: val_inj.
  rewrite val_insubd.
  done.
Qed.

Goal inupdownd "xxx" = off.
Proof.
  rewrite /inupdownd.
  Check insubd off "xxx" = off.             (* updown 型 *)
  apply: val_inj.
  rewrite val_insubd.
  done.
Qed.

(**
## insub の使い方 - もとの型からサブタイプ型の値を作る。

``insub x : option sT`` のとき x が sT に変換できるなら変換する。さもなければ None を返す。
*)
Check insub : string -> option updown.
Check @insub string (fun s => s \in EList) updown : string -> option updown.
(* 関数にして、値の型を明確にしておくことがふつうである。 *)
Definition inupdown (s : string) : option updown := insub s.

Goal inupdown "up" = Some up.
Proof.
  rewrite /inupdown.
  Check insub "up" = Some up.               (* option updown 型 *)
  by rewrite insubT.
Qed.

(* inudpdown 関数の値の型から、option updown 型とわかる。 *)
Goal inupdown "xxx" = None.
Proof.
  rewrite /inupdown.
  Check insub "xxx" = None.                 (* option updown 型 *)
  by rewrite insubF.
Qed.

(* 右辺が None で option updown とわからないので、:> をつける。 *)
Goal insub "xxx" = None :> option updown.
Proof.
  rewrite /inupdown.
  by rewrite insubF.
Qed.

(*
## 参考

ここでは、特別に Equality (eqType) を定義しない。
*)
Compute up == up.            (* string へのコアーションで成り立つ。 *)

(**
# MathComp のサブタイプの例

```
ssreflect/tuple.v:HB.instance Definition _ := [isSub for tval].
ssreflect/fintype.v:HB.instance Definition _ := [isSub of ordinal for nat_of_ord].
algebra/rat.v:Definition rat_isSub := Eval hnf in [isSub for valq].
algebra/poly.v:HB.instance Definition _ := [isSub for polyseq].

MathComp1 の [SubType for ...] だから、少し、わかりにくくなったかも。
```
*)

(**
## \val
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
## insubd

inord の例

``inord x : 'I_n`` のとき、``x < n`` なら x を 'I_n に変換する。さもなければ ord0 を返す。
``insubd ord0 x : 'I_n``
 *)
Check inord 2 : 'I_4.
Print inord.                  (* = fun n' : nat => [eta insubd ord0] *)
Check insubd ord0 : nat -> 'I_4.
Check @insubd nat (ltn^~ 4) 'I_4 ord0 : nat -> 'I_4.

Goal inord 2 = Ordinal (isT : 2 < 4).
Proof.
  rewrite /inord.
  Check insubd ord0 2 = Ordinal (isT : 2 < 4) :> 'I_4.
  apply: val_inj.
  rewrite val_insubd.
  done.
Qed.

Goal inord 4 = ord0 :> 'I_4.
Proof.
  rewrite /inord.
  Check insubd ord0 4 = ord0 :> 'I_4.
  apply: val_inj.
  rewrite val_insubd.
  done.
Qed.

(**
## insub

``insub x : option 'I_n`` のとき、``x < n`` なら x を 'I_n に変換する。さもなければ None を返す。
*)
Check insub 2 : option 'I_4.
Check @insub nat (ltn^~ 4) 'I_4 : nat -> option 'I_4.

Goal insub 2 = Some (Ordinal (isT : 2 < 4)). (* option 'I_4 *)
Proof.
  by rewrite insubT.
Qed.

Goal insub 4 = None :> option 'I_4. (* 右辺が None であるため、option 'I_4 とわからない。 *)
Proof.
  by rewrite insubF.
Qed.

(**
# サブタイプの補題 (acs_exercise5 で使用する)
 *)

(* val が単射である。 *)
Check @val_inj : forall (T : Type) (P : pred T) (sT : subType P), injective \val.
Check val_eqE : forall (T : eqType) (P : pred T) (sT : subEqType P) (u v : sT),
    (\val u == \val v) = (u == v).

(* val と insub でもとにもどる。 *)
Check @insubK : forall (T : Type) (P : pred T) (sT : subType P), ocancel insub \val.

(* val と insubd でもとにもどる。 *)
Check val_insubd : forall (T : Type) (P : pred T) (sT : subType P) (u : sT) (x : T),
    \val (insubd u x) = (if P x then x else \val u).
Check @insubdK : forall (T : Type) (P : pred T) (sT : subType P) (u0 : sT), {in P, cancel (insubd u0) \val}.

(* END *)
