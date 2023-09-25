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

(* rat の作り方 *)
Check GRing.isZmodule.Build rat addqA addqC add0q addNq.
Check zmodType.

Check GRing.Zmodule_isComRing.Build rat mulqA mulqC mul1q mulq_addl nonzero1q.
Check comRingType.

Check GRing.ComRing_isField.Build rat mulVq invq0.
Check fieldType.

Check Num.IntegralDomain_isLeReal.Build rat le_rat0D le_rat0M le_rat0_anti
  subq_ge0 (@le_rat_total 0%R) norm_ratN ge_rat0_norm lt_rat_def.
Check realFieldType.

Check Num.RealField_isArchimedean.Build rat rat_archimedean.
Check archiFieldType.







Check GRing.isSubringClosed.Build rat Qint_pred Qint_subring_closed.
Check GRing.isSemiringClosed.Build rat Qnat_pred Qnat_semiring_closed.
