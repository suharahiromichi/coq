From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

(* ssralg で定義される型 *)
     Check rat : nmodType.                  (* additive abelian monoid *)
     Check rat : zmodType.                  (* additive abelian group (Nmodule with an opposite) *)
     Check rat : semiRingType.              (* non-commutative semi rings *)
Fail Check rat : comSemiringType.           (* commutative semi rings *) (* MAY BE BUG *)
     Check rat : ringType.                  (* non-commutative rings (semi rings with an opposite) *)
     Check rat : comRingType.               (* commutative rings *)
     Check rat : unitRingType.              (* Rings whose units have computable inverses *)
     Check rat : comUnitRingType.           (* commutative UnitRing *)
(**) Check rat : idomainType.               (* integral, commutative, ring with partial inverses *)

     Check rat : fieldType.                 (* commutative fields *)
Fail Check rat : decFieldType.              (* fields with a decidable first order theory *)
Fail Check rat : closedFieldType.           (* 閉体 *)

(* ssrnum で定義される型 *)
     Check rat : porderZmodType.            (* join of Order.POrder and GRing.Zmodule *)
Fail Check rat : normedZmodType.            (* Zmodule with a norm *) (* MAY BE BUG *)
     Check rat : numDomainType.             (* Integral domain with an order and a norm *)
(**) Check rat : realDomainType.            (* Num domain where all elements are positive or negative *)

     Check rat : numFieldType.              (* Field with an order and a norm *)
Fail Check rat : numClosedFieldType.        (* Partially ordered Closed Field with conjugation *)
     Check rat : realFieldType.             (* Num Field where all elements are positive or negative *)
     Check rat : archiFieldType.            (* A Real Field with the archimedean axiom *)
Fail Check rat : rcfType.                   (* A Real Field with the real closed axiom *)
