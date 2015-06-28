(**
SSReflect もどきを作ってみる。

@suharahiromichi

2015_05_13

2015_06_28
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(* ******************* *)
(* 1. SSReflect の準備 *)
(* ******************* *)
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


(* ******************** *)
(* 2. bool に関する定理 *)
(* ******************** *)
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
Definition bool_eqMixin := EqMixin bool_eqP.            (* @EqMixin bool eqb bool_eqP. *)
Canonical Structure bool_eqType := EqType bool_eqMixin. (* @EqType bool bool_eqMixin. *)
(* Defineした後で、Canonical を宣言してもよい： *)
(* Definition bool_eqType := EqType bool_eqMixin. *)
(* Canonical Structure bool_eqType. *)
(*
bool_eqType を EqType... の Canonical Structure としたことで、 
特に指定せずとも EqType.. の具体例として bool_eqType を使えるようになる。
bool値どうしの比較を、EqType 上の同値関係 (eq_op, ==) を使って行えるようになる。
see. http://mathink.net/program/coq_setoid.html
*)
Print Canonical Projections.
(* bool <- sort ( bool_eqType ) *)

(* bool に対して、eq_op が使用可能になる。 *)
Check @eq_op bool_eqType true true.
Check true == true.


(* ******************* *)
(* 3. Viewのための定理 *)
(* ******************* *)
Lemma introTF :
  forall {P : Prop} {b c : bool},
    reflect P b ->
    (match c with
       | true => P
       | false => ~ P
     end) ->
    b = c.
Proof.
  intros P b c Hb.
  case c; case Hb; intros H1 H2.
  - reflexivity.
  - exfalso. now apply H1.
  - exfalso. now apply H2.
  - reflexivity.
Qed.

Lemma elimTF :
  forall {P : Prop} {b c : bool},
    reflect P b ->
    b = c ->
    (match c with
       | true => P
       | false => ~ P
     end).
Proof.
  intros P b c Hb Hbc.
  rewrite <- Hbc.
  now case Hb; intro H; apply H.
Qed.

Lemma elimT :
  forall {P : Prop} {b : bool}, reflect P b -> b -> P.
Proof.
  intros P b Hb.
  Check (@elimTF P b true Hb).
  now apply (@elimTF P b true Hb).
Qed.
    
Lemma introT :
  forall {P : Prop} {b : bool}, reflect P b -> P -> b.
Proof.
  intros P b Hb.
  Check (@introTF P b true Hb).
  now apply (@introTF P b true Hb).
Qed.


(* ********************* *)
(* 4. Reflectのための定理 *)
(* ********************* *)
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

Check (introT eqP').
Check (elimT eqP').

Goal true == true.
Proof.
  apply (introT eqP').                  (* apply/eqP *)
  (* Goal : true = true *)
  apply (elimT eqP').                   (* apply/eqP *)
  (* Goal : true == true *)
  apply (introT eqP').                  (* apply/eqP *)
  (* Goal : true = true *)
  reflexivity.                          (* true = true *)
Qed.

(* END *)
