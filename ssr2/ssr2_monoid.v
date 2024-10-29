(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun.

(******************************************************************************)
(* Tips for using lemmas in this file:                                        *)
(* To apply a lemma for a specific operator: if no special property is        *)
(* required for the operator, simply apply the lemma; if the lemma needs      *)
(* certain properties for the operator, make sure the appropriate instances   *)
(* are declared using, e.g., Check addn : Monoid.law _. to check that addn    *)
(* is equipped with the monoid laws.                                          *)
(******************************************************************************)
(* Interfaces for operator properties are packaged in the SemiGroup and       *)
(* Monoid submodules:                                                         *)
(*      SemiGroup.law == interface (keyed on the operator) for associative    *)
(*                       operators                                            *)
(*                       The HB class is SemiGroup.                           *)
(*  SemiGroup.com_law == interface for associative and commutative operators  *)
(*                       The HB class is SemiGroup.ComLaw.                    *)
(*     Monoid.law idx == interface for associative operators with identity    *)
(*                       element idx                                          *)
(*                       The HB class is Monoid.Law.                          *)
(* Monoid.com_law idx == extension of Monoid.law for operators that are also  *)
(*                       commutative                                          *)
(*                       The HB class is Monoid.ComLaw.                       *)
(* Monoid.mul_law abz == interface for operators with absorbing (zero)        *)
(*                       element abz                                          *)
(*                       The HB class is Monoid.MulLaw.                       *)
(* Monoid.add_law idx mop == extension of Monoid.com_law for operators over   *)
(*                       which operation mop distributes (mop will often also *)
(*                       have a Monoid.mul_law idx structure)                 *)
(*                       The HB class is Monoid.AddLaw.                       *)
(*   SemiGroup.Theory == submodule containing basic generic algebra lemmas    *)
(*                       for operators satisfying the SemiGroup interfaces    *)
(*      Monoid.Theory == submodule containing basic generic algebra lemmas    *)
(*                       for operators satisfying the Monoid interfaces,      *)
(*                       exports SemiGroup.Theory                             *)
(*       Monoid.simpm == generic monoid simplification rewrite multirule      *)
(*             oAC op == convert an AC operator op : T -> T -> T              *)
(*                       to a Monoid.com_law on option T                      *)
(* Monoid structures are predeclared for many basic operators: (_ && _)%B,    *)
(* (_ || _)%B, (_ (+) _)%B (exclusive or), (_ + _)%N, (_ * _)%N, maxn,        *)
(* gcdn, lcmn and (_ ++ _)%SEQ (list concatenation)                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SemiGroup.

HB.mixin Record isLaw T (op : T -> T -> T) := {
  opA : associative op;
}.

#[export]
HB.structure Definition Law T := {op of isLaw T op}.
Notation law := Law.type.

HB.mixin Record isCommutativeLaw T (op : T -> T -> T) := {
  opC : commutative op;
}.

#[export]
HB.structure Definition ComLaw T := {op of Law T op & isCommutativeLaw T op}.
Notation com_law := ComLaw.type.

HB.factory Record isComLaw T (op : T -> T -> T) := {
  opA : associative op;
  opC : commutative op;
}.

HB.builders Context T op of isComLaw T op.

HB.instance Definition _ := isLaw.Build T op opA.
HB.instance Definition _ := isCommutativeLaw.Build T op opC.

HB.end.

Module Import Exports. HB.reexport. End Exports.

Module Theory.

Section Theory.
Variables (T : Type).

Section Plain.
Variable mul : law T.
Lemma mulmA : associative mul. Proof. exact: opA. Qed.
End Plain.

Section Commutative.
Variable mul : com_law T.
Lemma mulmC : commutative mul. Proof. exact: opC. Qed.
Lemma mulmCA : left_commutative mul.
Proof. by move=> x y z; rewrite !mulmA [_ x _]mulmC. Qed.
Lemma mulmAC : right_commutative mul.
Proof. by move=> x y z; rewrite -!mulmA [_ y _]mulmC. Qed.
Lemma mulmACA : interchange mul mul.
Proof. by move=> x y z t; rewrite -!mulmA [_ y _]mulmCA. Qed.
End Commutative.

End Theory.

End Theory.

Include Theory.

End SemiGroup.
Export SemiGroup.Exports.

Module Monoid.

Export SemiGroup.

HB.mixin Record isMonoidLaw T (idm : T) (op : T -> T -> T) := {
  op1m : left_id idm op;
  opm1 : right_id idm op;
}.

#[export]
HB.structure Definition Law T idm :=
  {op of SemiGroup.Law T op & isMonoidLaw T idm op}.
Notation law := Law.type.

HB.factory Record isLaw T (idm : T) (op : T -> T -> T) := {
  opA : associative op;
  op1m : left_id idm op;
  opm1 : right_id idm op;
}.

HB.builders Context T idm op of isLaw T idm op.

HB.instance Definition _ := SemiGroup.isLaw.Build T op opA.
HB.instance Definition _ := isMonoidLaw.Build T idm op op1m opm1.

HB.end.

#[export]
HB.structure Definition ComLaw T idm :=
  {op of Law T idm op & isCommutativeLaw T op}.
Notation com_law := ComLaw.type.

HB.factory Record isComLaw T (idm : T) (op : T -> T -> T) := {
  opA : associative op;
  opC : commutative op;
  op1m : left_id idm op;
}.

HB.builders Context T idm op of isComLaw T idm op.

Lemma opm1 : right_id idm op. Proof. by move=> x; rewrite opC op1m. Qed.

HB.instance Definition _ := isLaw.Build T idm op opA op1m opm1.
HB.instance Definition _ := isCommutativeLaw.Build T op opC.

HB.end.

HB.mixin Record isMulLaw T (zero : T) (mul : T -> T -> T) := {
  mul_zerol : left_zero zero mul;
  mul_zeror : right_zero zero mul;
}.

#[export]
HB.structure Definition MulLaw T zero := {mul of isMulLaw T zero mul}.
Notation mul_law := MulLaw.type.

HB.mixin Record isAddLaw T (mul : T -> T -> T) (op : T -> T -> T) := {
  mul_op_Dl : left_distributive mul op;
  mul_op_Dr : right_distributive mul op;
}.

#[export]
HB.structure Definition AddLaw T zero mul :=
  {add of ComLaw T zero add & isAddLaw T mul add}.
Notation add_law := AddLaw.type.

Module Import Exports. HB.reexport. End Exports.

Section CommutativeAxioms.

Variable (T : Type) (zero one : T) (mul add : T -> T -> T).
Hypothesis mulC : commutative mul.

Lemma mulC_id : left_id one mul -> right_id one mul.
Proof. by move=> mul1x x; rewrite mulC. Qed.

Lemma mulC_zero : left_zero zero mul -> right_zero zero mul.
Proof. by move=> mul0x x; rewrite mulC. Qed.

Lemma mulC_dist : left_distributive mul add -> right_distributive mul add.
Proof. by move=> mul_addl x y z; rewrite !(mulC x). Qed.

End CommutativeAxioms.

Module Theory.

Export SemiGroup.Theory.

Section Theory.
Variables (T : Type) (idm : T).

Section Plain.
Variable mul : law idm.
Lemma mul1m : left_id idm mul. Proof. exact: op1m. Qed.
Lemma mulm1 : right_id idm mul. Proof. exact: opm1. Qed.
Lemma iteropE n x : iterop n mul x idm = iter n (mul x) idm.
Proof. by case: n => // n; rewrite iterSr mulm1 iteropS. Qed.
End Plain.

Section Mul.
Variable mul : mul_law idm.
Lemma mul0m : left_zero idm mul. Proof. exact: mul_zerol. Qed.
Lemma mulm0 : right_zero idm mul. Proof. exact: mul_zeror. Qed.
End Mul.

Section Add.
Variables (mul : T -> T -> T) (add : add_law idm mul).
Lemma addmA : associative add. Proof. exact: mulmA. Qed.
Lemma addmC : commutative add. Proof. exact: mulmC. Qed.
Lemma addmCA : left_commutative add. Proof. exact: mulmCA. Qed.
Lemma addmAC : right_commutative add. Proof. exact: mulmAC. Qed.
Lemma add0m : left_id idm add. Proof. exact: mul1m. Qed.
Lemma addm0 : right_id idm add. Proof. exact: mulm1. Qed.
Lemma mulmDl : left_distributive mul add. Proof. exact: mul_op_Dl. Qed.
Lemma mulmDr : right_distributive mul add. Proof. exact: mul_op_Dr. Qed.
End Add.

Definition simpm := (mulm1, mulm0, mul1m, mul0m, mulmA).

End Theory.

End Theory.
Include SemiGroup.Theory.
Include Theory.

End Monoid.
Export Monoid.Exports.

Section PervasiveMonoids.

Import Monoid.

HB.instance Definition _ := isComLaw.Build bool true andb andbA andbC andTb.

HB.instance Definition _ := isMulLaw.Build bool false andb andFb andbF.
HB.instance Definition _ := isComLaw.Build bool false orb orbA orbC orFb.
HB.instance Definition _ := isMulLaw.Build bool true orb orTb orbT.
HB.instance Definition _ := isComLaw.Build bool false addb addbA addbC addFb.
HB.instance Definition _ := isAddLaw.Build bool andb orb andb_orl andb_orr.
HB.instance Definition _ := isAddLaw.Build bool orb andb orb_andl orb_andr.
HB.instance Definition _ := isAddLaw.Build bool andb addb andb_addl andb_addr.

HB.instance Definition _ := isComLaw.Build nat 0 addn addnA addnC add0n.
HB.instance Definition _ := isComLaw.Build nat 1 muln mulnA mulnC mul1n.
HB.instance Definition _ := isMulLaw.Build nat 0 muln mul0n muln0.
HB.instance Definition _ := isAddLaw.Build nat muln addn mulnDl mulnDr.

HB.instance Definition _ := isComLaw.Build nat 0 maxn maxnA maxnC max0n.
HB.instance Definition _ := isAddLaw.Build nat muln maxn maxnMl maxnMr.

HB.instance Definition _ := isComLaw.Build nat 0 gcdn gcdnA gcdnC gcd0n.
HB.instance Definition _ := isAddLaw.Build nat muln gcdn muln_gcdl muln_gcdr.

HB.instance Definition _ := isComLaw.Build nat 1 lcmn lcmnA lcmnC lcm1n.
HB.instance Definition _ := isAddLaw.Build nat muln lcmn muln_lcml muln_lcmr.

HB.instance Definition _ T := isLaw.Build (seq T) nil cat
  (@catA T) (@cat0s T) (@cats0 T).

End PervasiveMonoids.

(* Unit test for the [...law of ...] Notations
Definition myp := addn. Definition mym := muln.
Canonical myp_mon := [law of myp].
Canonical myp_cmon := [com_law of myp].
Canonical mym_mul := [mul_law of mym].
Canonical myp_add := [add_law _ of myp].
Print myp_add.
Print Canonical Projections.
*)

HB.graph "Monoid.dot".
(*
% tred Monoid.dot | dot -T png > Monoid.png
 *)

(* END *)
