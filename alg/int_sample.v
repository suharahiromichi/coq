(**
algebra/ssrint.v の使い方
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From mathcomp Require Import ssralg ssrnum ssrint.

(**
# ssrnum までの構造を使えるようにする。
 *)
Import Order.TTheory.                       (* order.v *)
Import GRing.Theory.                        (* ssralg.v *)
Import Num.Def Num.Theory.                  (* ssrnum.v *)

(* int については、適宜以下をImportしていく。 *)
(* Import intZmod intRing intUnitRing intOrdered. *)

(**
# scope を有効にする。これはよくわかっていない。
 *)
Open Scope ring_scope.
Check 1 : (_ : semiRingType).
Open Scope int_scope.
Check 1 : int.

(**
# int の数学構造

## ssralg で定義される型
 *)
     Check int : nmodType.                  (* additive abelian monoid *)
     Check int : zmodType.                  (* additive abelian group (Nmodule with an opposite) *)
     Check int : semiRingType.              (* non-commutative semi rings *)
     Check int : comSemiRingType.           (* commutative semi rings *)
     Check int : ringType.                  (* non-commutative rings (semi rings with an opposite) *)
     Check int : comRingType.               (* commutative rings *)
     Check int : unitRingType.              (* Rings whose units have computable inverses *)
     Check int : comUnitRingType.           (* commutative UnitRing *)
(**) Check int : idomainType.               (* 整域 integral, commutative, ring with partial inverses *)

Fail Check int : fieldType.                 (* commutative fields *)
Fail Check int : decFieldType.              (* fields with a decidable first order theory *)
Fail Check int : closedFieldType.           (* 閉体 *)

(**
## ssrnum で定義される型
 *)
     Check int : porderZmodType.            (* join of Order.POrder and GRing.Zmodule *)
Fail Check int : normedZmodType.            (* Zmodule with a norm *)
     Check int : numDomainType.             (* Integral domain with an order and a norm *)
(**) Check int : realDomainType.            (* Num domain where all elements are positive or negative *)

Fail Check int : numFieldType.              (* Field with an order and a norm *)
Fail Check int : numClosedFieldType.        (* Partially ordered Closed Field with conjugation *)
Fail Check int : realFieldType.             (* Num Field where all elements are positive or negative *)
Fail Check int : archiFieldType.            (* A Real Field with the archimedean axiom *)
Fail Check int : rcfType.                   (* A Real Field with the real closed axiom *)


(*
# int のつくりかた
 *)
(**
```
HB.factory Record isZmodule V of Choice V := {
  zero : V;
  opp : V -> V;
  add : V -> V -> V;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add
}.
```
*)
Import intZmod.
Check @GRing.isZmodule.Build int
  0
  oppz
  addz
  addzA
  addzC
  add0z
  addNz
  : GRing.isZmodule.axioms_ int _ _.

Check int : zmodType.                   (* int が Zmoduleになった。 *)

(**
```
HB.factory Record Zmodule_isComRing R of Zmodule R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mulrC : commutative mul;
  mul1r : left_id one mul;
  mulrDl : left_distributive mul add;
  oner_neq0 : one != zero
}.
```
*)
Import intRing.
Check intRing.comMixin.
Check @GRing.Zmodule_isComRing.Build int
  1
  mulz
  mulzA mulzC mul1z mulz_addl nonzero1z
  : GRing.Zmodule_isComRing.axioms_ int _ _ _ _.

Check nonzero1z : 1%Z != 0.
Goal 1%Z != 0.
Proof. done. Qed.

Check int : comRingType.                  (* int が可換環になった。 *)

(**
```
HB.factory Record ComRing_hasMulInverse R of ComRing R := {
  unit : {pred R};
  inv : R -> R;
  mulVx : {in unit, left_inverse 1 inv *%R};
  unitPl : forall x y, y * x = 1 -> unit x;
  invr_out : {in [predC unit], inv =1 id}
}.
```
*)
Import intUnitRing.
Check @GRing.ComRing_hasMulInverse.Build int
  unitz
  invz
  mulVz
  unitzPl
  invz_out
  : GRing.ComRing_hasMulInverse.axioms_ int _ _ _ _ _ _.

(* unit *)
Check unitz : qualifier 1 int.
Print unitz.       (* = [qualify a n | (n == 1) || (n == -1)] *)
Compute 1 \in unitz.                        (* true *)
Compute 0 \in unitz.                        (* false *)
Compute -1 \in unitz.                       (* true *)
Compute 2 \in unitz.                        (* false *)
Compute 2 \is a unitz.                      (* false *)
Locate "_ \in _".   (* Notation "x \in A" := (in_mem x (mem A)) *)
Locate "_ \is a _". (* Notation "x \is 'a' A" := (in_mem x (mem A)) *)

(* inv *)
Check invz : int -> int.
Compute invz 1.                             (* 1 *)
Compute invz 0.                             (* 0 *)
Compute invz (-1).                          (* -1 *)
Compute invz 2.                             (* 2 *)

(* mulVx *)
Check mulVz : {in unitz, left_inverse 1 invz  *%R}.
Print left_inverse.
(* fun (S T R : Type) (e : R) (inv : T -> S) (op : S -> T -> R) => forall x : T, op (inv x) x = e *)
(*                                                                               ~~~~~~~~~~~~~~~~ *)
Goal {in unitz, left_inverse 1 invz  *%R}.
(* ,の左は、``forall n, n \in unitz`` *)
(* ,の右は、opまで与えているので ``forall n, invz n * n = 1`` *)
Proof.
  move=> n.
  (* n \is a unitz -> invz n * n = 1 *)
  move/pred2P.
  (* n = 1 \/ n = -1 -> invz n * n = 1 *)
  case.
  - by move=> ->.
  - by move=> ->.
Qed.    

(* unitPl *)
Check unitzPl : forall m n : int, n * m = 1%R -> m \is a unitz.
Goal forall m n : int, n * m = 1%R -> m \is a unitz.
Proof.
  move=> m n.
  Check qualifE : forall (n : nat) (T : Type) (p : {pred T}) (x : T), (x \in Qualifier n (T:=T) p) = p x.
  rewrite qualifE => /eqP.
  case: m => m.
  - rewrite mulzn_eq1.
    by move=> /andP [] _ /eqP ->.
  - rewrite ssrint.NegzE mulrN -mulNr.
    rewrite mulzn_eq1.
    by move=> /andP [] _ /eqP ->.
Qed.

Check invz_out : {in [predC unitz], invz =1 id}.
Goal {in [predC unitz], invz =1 id}.
Proof.
  move=> x.
  (* x \in [predC unitz] -> invz x = x *)
  rewrite inE.
  (* x \isn't a unitz -> invz x = x *)
  rewrite /negb.
  (* (if x \is a unitz then false else true) -> invz x = x *)
  done.
Qed.

Check int : comUnitRingType.    (* int が逆元をもつ可換環になった。 *)

HB.howto comUnitRingType.
HB.about GRing.ComRing_hasMulInverse.
HB.about GRing.ComRing_hasMulInverse.mulVx.

(**
```
HB.mixin Record ComUnitRing_isIntegral R of ComUnitRing R := {
  mulf_eq0_subproof : integral_domain_axiom R;
}.
```
*)
Check intUnitRing.idomain_axiomz :          (* 整域公理 *)
  forall m n : int, (m * n)%R = 0%R -> (m == 0%R) || (n == 0%R).
Check GRing.ComUnitRing_isIntegral.Build int
  intUnitRing.idomain_axiomz.

(* idomain_axiomz 整域公理 *)
Check idomain_axiomz : forall m n : int, m * n = 0 -> (m == 0) || (n == 0).
Goal forall m n : int, m * n = 0 -> (m == 0) || (n == 0).
Proof.
  case=> m [] n //= /eqP.
  - rewrite -PoszM [_ == _]muln_eq0.
    done.
  - rewrite (ssrint.NegzE, mulrN, mulNr).
    rewrite oppr_eq0.
    rewrite [_ == _]muln_eq0.
    done.
  - rewrite 2!(ssrint.NegzE, mulrN, mulNr).
    rewrite oppr_eq0 -PoszM.
    rewrite [_ == _]muln_eq0.
    done.
Qed.

Check int : idomainType.                    (* int が整域になった。 *)

(**
```
HB.factory Record IntegralDomain_isLeReal R of GRing.IntegralDomain R := {
  Rle : rel R;
  Rlt : rel R;
  norm : R -> R;
  le0_add   : forall x y, Rle 0 x -> Rle 0 y -> Rle 0 (x + y);
  le0_mul   : forall x y, Rle 0 x -> Rle 0 y -> Rle 0 (x * y);
  le0_anti  : forall x, Rle 0 x -> Rle x 0 -> x = 0;
  sub_ge0   : forall x y, Rle 0 (y - x) = Rle x y;
  le0_total : forall x, Rle 0 x || Rle x 0;
  normN     : forall x, norm (- x) = norm x;
  ge0_norm  : forall x, Rle 0 x -> norm x = x;
  lt_def    : forall x y, Rlt x y = (y != x) && Rle x y;
}.
```
*)
Import intOrdered.
Check @Num.IntegralDomain_isLeReal.Build int
  lez
  ltz
  absz                                      (* normz *)
  lez_add
  lez_mul
  lez_anti
  subz_ge0
  (lez_total 0)
  normzN
  gez0_norm
  ltz_def
  : Num.IntegralDomain_isLeReal.axioms_ int _ _ _ _ _ _ _ _.

Check ltz_def : forall m n : int, ltz m n = (n != m) && lez m n.
Goal forall m n, (ltz m n) = (n != m) && (lez m n).
Proof.
  by move=> [] m [] n //=; rewrite (ltn_neqAle, leq_eqVlt) // eq_sym.
Qed.

Check int : realDomainType.                 (* int が...になった。 *)
(* orderとnormがある整域 numDomain で、要素が正か負である。 *)

(* END *)
