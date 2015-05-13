(**
SSReflect もどきを作ってみる。

@suharahiromichi
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Notation "~" := not.

Inductive reflect (P : Prop) : bool -> Set :=
| ReflectT :   P -> reflect P true
| ReflectF : ~ P -> reflect P false.

Definition axiom T e :=
  forall x y : T, reflect (x = y) (e x y).
(*
Definition pred T := T -> bool.
Definition rel T := T -> pred T.
*)
Definition rel T := T -> T -> bool.

Record mixin_of (T : Type) :=
  EqMixin {                                 (* Mixin *)
      op : rel T;
      a : axiom op
    }.

Record eqType :=                            (* type *)
  EqType {                                  (* Pack *)
      sort :> Type;
      m : mixin_of sort
    }.

Print Graph.                                (* コアーション *)
(* [sort] : type >-> Sortclass *)

Definition eq_op (T : eqType) := op (m T).
Check eq_op : forall T : eqType, rel T.

Definition eqP (T : eqType) := axiom (@eq_op T).
Check eqP : eqType -> Type.

Notation "x == y" := (eq_op x y) (at level 70, no associativity).

(* **** *)
(* bool *)
(* **** *)
Require Import Bool.

Lemma iffP : forall (P Q : Prop) (b : bool),
               Top.reflect P b -> (P -> Q) -> (Q -> P) -> Top.reflect Q b.
Admitted.

Lemma idP : forall b1 : bool, Top.reflect (b1 = true) b1.
Admitted.

Lemma bool_eqP : axiom eqb.
Proof.
  unfold axiom.
  intros x y.
  apply (iffP (idP (eqb x y))).
  - unfold eqb.
    now case x; case y.
  - unfold eqb.
    now case x; case y.
Qed.

Fail Check true == true.

(* ここここ *)
Definition bool_eqMixin := EqMixin bool_eqP.
Canonical bool_eqType := EqType (* bool *) bool_eqMixin.
Print Canonical Projections.
(* bool <- sort ( bool_eqType ) *)

(* bool に対して、eq_op が使用可能になる。 *)
Check true == true : bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Check @idP.

(* END *)
