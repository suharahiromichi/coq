(**
finset_eqType, finset_choiceType, finset_countType, finset_finType を求める。
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

(**
## subType
 *)

Section SetType.

Variable T : finType.

Inductive set_type : predArgType := FinSet of {ffun pred T}.
Definition finfun_of_set A := let: FinSet f := A in f.
Definition set_of of phant T := set_type.
Identity Coercion type_of_set_of : set_of >-> set_type.

Canonical set_subType := Eval hnf in [newType for finfun_of_set].

(**
## eqType
 *)

Definition set_eqMixin := Eval hnf in [eqMixin of set_type by <:].
Canonical set_eqType := Eval hnf in EqType set_type set_eqMixin.

(**
## choiceType
 *)

Definition set_choiceMixin := [choiceMixin of set_type by <:].
Canonical set_choiceType := Eval hnf in ChoiceType set_type set_choiceMixin.

(**
## countType
*)

Definition set_countMixin := [countMixin of set_type by <:].
Canonical set_countType := Eval hnf in CountType set_type set_countMixin.
Canonical set_subCountType := Eval hnf in [subCountType of set_type].


(**
## finType
 *)

Definition set_finMixin := [finMixin of set_type by <:].
Canonical set_finType := Eval hnf in FinType set_type set_finMixin.
Canonical set_subFinType := Eval hnf in [subFinType of set_type].

End SetType.


(**
## おまけ
 *)

Section BasicSetTheory.

Variable T : finType.
Implicit Types (x : T) (A B : {set T}) (pA : pred T).

(*
Canonical set_of_subType := Eval hnf in [subType of {set T}].
Canonical set_of_eqType := Eval hnf in [eqType of {set T}].
Canonical set_of_choiceType := Eval hnf in [choiceType of {set T}].
Canonical set_of_countType := Eval hnf in [countType of {set T}].
Canonical set_of_subCountType := Eval hnf in [subCountType of {set T}].
Canonical set_of_finType := Eval hnf in [finType of {set T}].
Canonical set_of_subFinType := Eval hnf in [subFinType of {set T}].
 *)

Lemma in_set pA x : x \in finset pA = pA x.
Proof. by rewrite [@finset]unlock unlock [x \in _]ffunE. Qed.

Lemma setP A B : A =i B <-> A = B.
Proof.
by split=> [eqAB|-> //]; apply/val_inj/ffunP=> x; have:= eqAB x; rewrite unlock.
Qed.

Definition set0 := [set x : T | false].
Definition setTfor (phT : phant T) := [set x : T | true].

Lemma in_setT x : x \in setTfor (Phant T).
Proof. by rewrite in_set. Qed.

Lemma eqsVneq A B : {A = B} + {A != B}.
Proof. exact: eqVneq. Qed.

End BasicSetTheory.


(* END *)
