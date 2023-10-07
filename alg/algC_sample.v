(**
field/algC.v の使用例
*)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_field.

(**
# ssrnum までの構造を使えるようにする。
 *)
Import Order.TTheory.                       (* order.v *)
Import GRing.Theory.                        (* ssralg.v *)
Import Num.Def Num.Theory.                  (* ssrnum.v *)

(**
# scope を有効にする。これはよくわかっていない。
 *)
Open Scope ring_scope.
Check 1 : (_ : semiRingType).

(**
# algC の数学構造

algC型は、numClosedFieldType型のインスタンスである。

## ssralg で定義される型
 *)
Check algC : nmodType.
Check algC : zmodType.
Check algC : semiRingType.
Check algC : comSemiRingType.
Check algC : ringType.
Check algC : comRingType.                   (* 可換環 *)
Check algC : unitRingType.
Check algC : comUnitRingType.
Check algC : idomainType.
Check algC : fieldType.                     (* 整域 *)
Check algC : decFieldType.
Check algC : closedFieldType.               (* 閉体 *)

(**
## ssrnum で定義される型
 *)
Check algC : numDomainType. (* Integral domain with an order and a norm *)
Fail Check algC : realDomainType. (* Num domain where all elements are positive or negative *)
Check algC : numFieldType.
Check algC : numClosedFieldType.
Fail Check algC : realFieldType.
Fail Check algC : realFieldType.
Fail Check algC : rcfType.

Search algC.                    (* これで補題が見つからなかったら、 *)
Search numClosedFieldType.      (* これで探す。 *)

(* 予備 *)
Check Num.IntegralDomain_isNumRing.Build algC.
Check Num.NumField_isImaginary.Build algC.
Check GRing.ClosedField.on algC.
Check isComplex.Build algC.
Check isCountable.Build algC.

Check GRing.isZmodule.Build algC.
Fail Check GRing.isAdditive.Build algC.
Check GRing.Zmodule_isComRing.Build algC.
Check GRing.ComRing_isField.Build algC.
Check Field_isAlgClosed.Build algC.
Check isComplex.Build algC.
Fail Check GRing.isSubringClosed.Build algC.
Fail Check GRing.isSemiringClosed.Build algC.
Fail Check GRing.isZmodClosed.Build algC.
Fail Check GRing.isDivringClosed.Build algC.

(* END *)
