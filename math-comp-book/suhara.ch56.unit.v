(**
unit_eqType, unit_choiceType, unit_countType, unit_finType を求める。
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

(**
## eqType
 *)
Check @EqMixin : forall (T : Type) (op : rel T),
    Equality.axiom (T:=T) op -> Equality.mixin_of T.

Definition eqUnit (_ _ : unit) := true.     (* op *)

(* boolean とのリフレクションが成り立つ *)
Lemma unit_eqP : @Equality.axiom unit eqUnit. (* axiom *)
Proof.
    by do 2!case; left.
Qed.

Definition unit_eqMixin := @EqMixin unit eqUnit unit_eqP.
(* Definition unit_eqMixin := EqMixin unit_eqP. *)
Canonical unit_eqType := Eval hnf in EqType unit unit_eqMixin.


(**
## choiceType
 *)
Check @CanChoiceMixin : forall (T : choiceType) (sT : Type) (f : sT -> T) (f' : T -> sT),
    cancel f f' -> choiceMixin sT.

(* boolによるピックアップができること。 *)
Definition pickUnit : unit -> bool := xpredT.
Definition unpickUnit : bool -> unit := fun _ => tt.

(* pickとunpickで消せること。 *)
Lemma bool_of_unitK : cancel pickUnit unpickUnit.
Proof.
    by case.
Qed.

Definition unit_choiceMixin := @CanChoiceMixin bool_choiceType unit
                                               pickUnit unpickUnit 
                                               bool_of_unitK.
(* Definition unit_choiceMixin := CanChoiceMixin bool_of_unitK. *)
Canonical unit_choiceType := Eval hnf in ChoiceType unit unit_choiceMixin.


(**
## countType
 *)
Check @CanCountMixin : forall (T : countType) (sT : Type) (f : sT -> T) (f' : T -> sT),
    cancel f f' -> Countable.mixin_of sT.

Definition unit_countMixin := @CanCountMixin bool_countType unit
                                             pickUnit unpickUnit
                                             bool_of_unitK.
(* Definition unit_countMixin := CanCountMixin bool_of_unitK. *)
Canonical unit_countType := Eval hnf in CountType unit unit_countMixin.


(**
## finType
 *)
Check @FinMixin : forall (T : countType) (e : seq T),
    Finite.axiom (T:=T) e -> Finite.mixin_of T.

Definition enumUnit := [:: tt].             (* enum *)

(* enum のなかに 型の要素がひとつづつ存在する。 *)
Lemma unit_enumP : @Finite.axiom unit_eqType enumUnit.   (* axiom *)
Proof.
    by case.
Qed.

Definition unit_finMixin := @FinMixin unit_countType enumUnit unit_enumP.
(* Definition unit_finMixin := Eval hnf in FinMixin unit_enumP. *)
Canonical unit_finType := Eval hnf in FinType unit unit_finMixin.

Lemma card_unit : #|{: unit}| = 1.
Proof.
    by rewrite cardT enumT unlock.
Qed.

(* END *)
