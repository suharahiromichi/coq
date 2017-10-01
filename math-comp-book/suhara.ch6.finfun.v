(**
finfun_eqType, finfun_choiceType, finfun_countType, finfun_finType を求める。
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

(**
## subType
 *)

Section Def.

Variables (aT : finType) (rT : Type).

Inductive finfun_type : predArgType := Finfun of #|aT|.-tuple rT.

Definition finfun_of of phant (aT -> rT) := finfun_type.

Identity Coercion type_of_finfun : finfun_of >-> finfun_type.

Definition fgraph f := let: Finfun t := f in t.

Canonical finfun_subType := Eval hnf in [newType for fgraph].

End Def.


(**
## eqType
 *)


Section EqTheory.

Variables (aT : finType) (rT : eqType).
Notation fT := {ffun aT -> rT}.
Implicit Types (y : rT) (D : pred aT) (R : pred rT) (f : fT).

Definition finfun_eqMixin :=
  Eval hnf in [eqMixin of finfun_type aT rT by <:].
Canonical finfun_eqType := Eval hnf in EqType _ finfun_eqMixin.
Canonical finfun_of_eqType := Eval hnf in [eqType of fT].


End EqTheory.


(**
## choiceType

Codomain が choice可能 なら、finfunはchoice可能である。
 *)

Definition finfun_choiceMixin aT (rT : choiceType) :=
  [choiceMixin of finfun_type aT rT by <:].
Canonical finfun_choiceType aT rT :=
  Eval hnf in ChoiceType _ (finfun_choiceMixin aT rT).
Canonical finfun_of_choiceType (aT : finType) (rT : choiceType) :=
  Eval hnf in [choiceType of {ffun aT -> rT}].

(**
## countType

Codomain が countablee なら、finfunはcountableである。
 *)

Definition finfun_countMixin aT (rT : countType) :=
  [countMixin of finfun_type aT rT by <:].
Canonical finfun_countType aT (rT : countType) :=
  Eval hnf in CountType _ (finfun_countMixin aT rT).
Canonical finfun_of_countType (aT : finType) (rT : countType) :=
  Eval hnf in [countType of {ffun aT -> rT}].
Canonical finfun_subCountType aT (rT : countType) :=
  Eval hnf in [subCountType of finfun_type aT rT].
Canonical finfun_of_subCountType (aT : finType) (rT : countType) :=
  Eval hnf in [subCountType of {ffun aT -> rT}].


(**
## finType

Codomain が finType なら、finfunはfinTypeである。
 *)

Section FinTheory.

Variables aT rT : finType.
Notation fT := {ffun aT -> rT}.
Notation ffT := (finfun_type aT rT).
Implicit Types (D : pred aT) (R : pred rT) (F : aT -> pred rT).

Definition finfun_finMixin := [finMixin of ffT by <:].
Canonical finfun_finType := Eval hnf in FinType ffT finfun_finMixin.
Canonical finfun_subFinType := Eval hnf in [subFinType of ffT].
(* Canonical finfun_of_finType := Eval hnf in [finType of fT for finfun_finType]. *)
Canonical finfun_of_subFinType := Eval hnf in [subFinType of fT].

End FinTheory.
 

(* END *)
