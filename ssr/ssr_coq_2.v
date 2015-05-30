(**
SSReflect もどきを作ってみる。

@suharahiromichi

2015_05_13
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

Definition rel T := T -> T -> bool.
Check rel : Type -> Type.

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


Coercion is_true : bool >-> Sortclass. (* Prop *)
Print Graph.                           (* コアーション *)
(* [is_true] : bool >-> Sortclass *)

(* **** *)
(* bool *)
(* **** *)
Lemma iffP : forall (P Q : Prop) (b : bool),
               reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Proof.
  intros P Q b HPb HPQ HQP.
  case HPb; intros HP.
  - apply ReflectT. auto.
  - apply ReflectF. auto.
Qed.

Lemma idP : forall b : bool, reflect b b.
Proof.
  intros b.
  case b.
  - now apply ReflectT.
  - now apply ReflectF.
Qed.

Definition eqb (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

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

Fail Check @eq_op bool_eqType true true.
Fail Check true == true.

(* eqb と eq の違い。 *)
(* すでに [is_true] : bool >-> Sortclass のコアーションが有効なので、 *)
Check eqb : bool -> bool -> bool.
Check eqb : bool -> bool -> Prop.
Check eqb : rel bool.
Check eq : bool -> bool -> Prop.
Fail Check eq : bool -> bool -> bool.
Fail Check le : rel bool.

(* ここここ *)
Definition bool_eqMixin := EqMixin bool_eqP.
Definition bool_eqType := @EqType bool bool_eqMixin.
Canonical Structure bool_eqType.
Print Canonical Projections.
(* bool <- sort ( bool_eqType ) *)

(* bool に対して、eq_op が使用可能になる。 *)
Check @eq_op bool_eqType true true.
Check true == true.

Lemma introTF :
  forall {P : Prop} {b c : bool},
    reflect P b ->
    (match c with
       | true => P
       | false => ~P end) ->
    b = c.
Proof.
  intros P b c Hb.
  case c; case Hb; intros H1 H2.
  - reflexivity.
  - exfalso. now apply H1.
  - exfalso. now apply H2.
  - reflexivity.
Qed.

Lemma eqP' :
  forall {x y : bool}, reflect (x = y) (x == y).
Proof.
  intros x y.
  now case x; case y; constructor.
(*
  now apply ReflectT.
  now apply ReflectF.
  now apply ReflectF.
  now apply ReflectT.
*)
Qed.

Goal true == true.
Proof.
  now apply (introTF eqP').                 (* apply/eqP *)
Qed.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(* END *)

