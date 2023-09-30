(**
ssrnum.v サンプル
*)
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From mathcomp Require Import ssralg ssrnum.

(**
# 型の階層図
*)

(**
```
zmodType
|\
| +-------------------+
|                      \
porderZmodType          normedZmodType
|                      /
| +-------------------+
|/
numDomainType
|
|
realDomainType
```
*)

Check Num.sqrt : (_ : rcfType) -> (_ : rcfType).
Import GRing.Theory.
Import Num.
Import Num.Theory.
Import Num.Def.

Local Open Scope ring_scope.


(* k-coq Exercise 3.5.1. *)

Variable R : rcfType.

Lemma l1 : (@sqrt R (4 + @sqrt R 3 *+ 2)) ^+ 2 = 4 + @sqrt R 3 *+ 2.
Proof.
  rewrite sqr_sqrtr //.
  apply: Internals.addr_ge0 => //.
  rewrite mulrn_wge0 //.
  by rewrite sqrtr_ge0.
Qed.

Lemma l2 : (@sqrt R 3 + 1) ^+ 2 = 4 + @sqrt R 3 *+ 2.
Proof.
  rewrite sqrrD1 sqr_sqrtr //.
  rewrite addrAC.
  have -> : 3 + 1 = 4 by move=> R; rewrite natr1.
  done.
Qed.

Goal @sqrt R (4 + @sqrt R 3 *+ 2) = @sqrt R 3 + 1.
Proof.
  apply/eqP.
  Check (@eqrXn2 R 2 _ _).
  rewrite -(@eqrXn2 R 2 _ _) //.
  - by rewrite l1 l2.
  - by rewrite sqrtr_ge0.
  - by rewrite addr_ge0 // sqrtr_ge0.
Qed.

(* END *)
