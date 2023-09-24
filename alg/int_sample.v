From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From mathcomp Require Import ssralg ssrnum ssrint.

About int.

(* ssralg で定義される型 *)
     Check int : nmodType.                  (* additive abelian monoid *)
     Check int : zmodType.                  (* additive abelian group (Nmodule with an opposite) *)
     Check int : semiRingType.              (* non-commutative semi rings *)
Fail Check int : comSemiringType.           (* commutative semi rings *)
     Check int : ringType.                  (* non-commutative rings (semi rings with an opposite) *)
     Check int : comRingType.               (* commutative rings *)
     Check int : unitRingType.              (* Rings whose units have computable inverses *)
     Check int : comUnitRingType.           (* commutative UnitRing *)
     Check int : idomainType.               (* integral, commutative, ring with partial inverses *)
Fail Check int : fieldType.                 (* commutative fields *)
Fail Check int : decFieldType.
Fail Check int : closedFieldType.

(* ssrnum で定義される型 *)
     Check int : porderZmodType.            (* join of Order.POrder and GRing.Zmodule *)
Fail Check int : normedZmodType.            (* Zmodule with a norm *)
     Check int : numDomainType.             (* Integral domain with an order and a norm *)
     Check int : realDomainType.            (* Num domain where all elements are positive or negative *)
Fail Check int : numFieldType.              (* Field with an order and a norm *)
Fail Check int : numClosedFieldType.        (* Partially ordered Closed Field with conjugation *)
Fail Check int : realFieldType.             (* Num Field where all elements are positive or negative *)
Fail Check int : archiFieldType.
Fail Check int : rcfType.



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
