From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From mathcomp Require Import ssralg ssrnum ssrint.

About int.

(* ssralg で定義される型 *)
     Check int : nmodType.                  (* additive abelian monoid *)
     Check int : zmodType.                  (* additive abelian group (Nmodule with an opposite) *)
     Check int : semiRingType.              (* non-commutative semi rings *)
Fail Check int : comSemiringType.           (* commutative semi rings *) (* MAY BE BUG *)
     Check int : ringType.                  (* non-commutative rings (semi rings with an opposite) *)
     Check int : comRingType.               (* commutative rings *)
     Check int : unitRingType.              (* Rings whose units have computable inverses *)
     Check int : comUnitRingType.           (* commutative UnitRing *)
(**) Check int : idomainType.               (* integral, commutative, ring with partial inverses *)

Fail Check int : fieldType.                 (* commutative fields *)
Fail Check int : decFieldType.              (* fields with a decidable first order theory *)
Fail Check int : closedFieldType.           (* 閉体 *)

(* ssrnum で定義される型 *)
     Check int : porderZmodType.            (* join of Order.POrder and GRing.Zmodule *)
Fail Check int : normedZmodType.            (* Zmodule with a norm *) (* MAY BE BUG *)
     Check int : numDomainType.             (* Integral domain with an order and a norm *)
(**) Check int : realDomainType.            (* Num domain where all elements are positive or negative *)

Fail Check int : numFieldType.              (* Field with an order and a norm *)
Fail Check int : numClosedFieldType.        (* Partially ordered Closed Field with conjugation *)
Fail Check int : realFieldType.             (* Num Field where all elements are positive or negative *)
Fail Check int : archiFieldType.            (* A Real Field with the archimedean axiom *)
Fail Check int : rcfType.                   (* A Real Field with the real closed axiom *)


(*
int のつくりかた
 *)
Check intZmod.Mixin : GRing.isZmodule.axioms_ int _ _.
Import intZmod.
Check GRing.isZmodule.Build int addzA addzC add0z addNz.
Check zmodType.

Check intRing.comMixin : GRing.Zmodule_isComRing.axioms_ int _ _ _ _.
Import intRing.
Check GRing.Zmodule_isComRing.Build int mulzA mulzC mul1z mulz_addl nonzero1z.
Check comRingType.

Check intUnitRing.comMixin : GRing.ComRing_hasMulInverse.axioms_ int _ _ _ _ _ _.
Check comUnitRingType.

Check intUnitRing.idomain_axiomz : forall m n : int, (m * n)%R = 0%R -> (m == 0%R) || (n == 0%R).
Check GRing.ComUnitRing_isIntegral.Build int intUnitRing.idomain_axiomz.
Check idomainType.

Check intOrdered.Mixin : Num.IntegralDomain_isLeReal.axioms_ int _ _ _ _ _ _ _ _.
Import intOrdered.
Check Num.IntegralDomain_isLeReal.Build int
  lez_add lez_mul lez_anti subz_ge0 (lez_total 0) normzN gez0_norm ltz_def.
Check realDomainType.

















Check intZmod.Mixin : GRing.isZmodule.axioms_ int _ _.
Check zmodType.
Check idomainType.

Check intRing.comMixin : GRing.Zmodule_isComRing.axioms_ int _ _ _ _.
Check comRingType.

Check intUnitRing.comMixin : GRing.ComRing_hasMulInverse.axioms_ int _ _ _ _ _ _.
Check comUnitRingType.

Check intUnitRing.idomain_axiomz : forall m n : int, (m * n)%R = 0%R -> (m == 0%R) || (n == 0%R).
Check GRing.ComUnitRing_isIntegral.Build int intUnitRing.idomain_axiomz.
Check idomainType.

Check intOrdered.Mixin : Num.IntegralDomain_isLeReal.axioms_ int _ _ _ _ _ _ _ _.
Check realDomainType.




Check HB_unnamed_mixin_4.
Check HB_unnamed_mixin_5.
Check HB_unnamed_mixin_6.
Check HB_unnamed_mixin_7.
Check HB_unnamed_mixin_8.
Check HB_unnamed_mixin_9.
Check HB_unnamed_mixin_10.
Check HB_unnamed_mixin_11.
Check HB_unnamed_mixin_12.
Check HB_unnamed_mixin_14.
Check HB_unnamed_mixin_15.
Check HB_unnamed_mixin_16.
Check HB_unnamed_mixin_17.
Check HB_unnamed_mixin_20.
Check HB_unnamed_mixin_21.
Check HB_unnamed_mixin_22.
Check HB_unnamed_mixin_23.
Check HB_unnamed_mixin_24.
Check HB_unnamed_mixin_26.
Check HB_unnamed_mixin_27.
Check HB_unnamed_mixin_28.
Check HB_unnamed_mixin_29.
Check HB_unnamed_mixin_30.
Check HB_unnamed_mixin_31.
Check HB_unnamed_mixin_33.



(*
     Check int : lmodType R.
     Check int : lalgType R.
     Check int : algType R.
     Check int : comAlgType R.
*)
(*
     Check int : unitAlgType R.
     Check int : comUnitAlgType R.
*)                 

(*
ssrint.v

HB.instance Definition _ := intZmod.Mixin.
HB.instance Definition _ := intRing.comMixin.
HB.instance Definition _ := intUnitRing.comMixin.
HB.instance Definition _ := intOrdered.Mixin.

Definition Mixin := GRing.isZmodule.Build int addzA addzC add0z addNz.
Definition comMixin := GRing.Zmodule_isComRing.Build int
Definition comMixin := GRing.ComRing_hasMulInverse.Build int
Definition Mixin := Num.IntegralDomain_isLeReal.Build int
 *)


  (*
ssralg.v:HB.factory Record isZmodule V of Choice V := {
ssralg.v:HB.factory Record Zmodule_isComRing R of Zmodule R := {
ssralg.v:HB.factory Record ComRing_hasMulInverse R of ComRing R := {
ssrnum.v:HB.factory Record IntegralDomain_isLeReal R of GRing.IntegralDomain R := {

*)
