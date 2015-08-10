(**
SSReflect もどきを作ってみる。

@suharahiromichi

2015_05_13

2015_06_28

2015_07_29
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

Definition rel (T : Type) := T -> T -> bool.
Check rel : Type -> Type.

Definition axiom (T : Type) (e : rel T) :=
  forall x y : T, reflect (x = y) (e x y).
Check axiom : forall T : Type, rel T -> Type.

Record mixin_of (T : Type) :=
  EqMixin {                                 (* Mixin *)
      op : rel T;                           (* T -> T -> bool でもよい。 *)
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
Check eq_op : forall T : eqType, T -> T -> bool.

Lemma eqP T : axiom (@eq_op T).
Proof.
  unfold axiom.
  case T.
  intros sort m.
  now apply m.
Qed.
Check eqP : forall T : eqType, axiom (@eq_op T).

Notation "x == y" := (eq_op x y) (at level 70, no associativity).

Coercion is_true : bool >-> Sortclass. (* Prop *)
Print Graph.                           (* コアーション *)
(* [is_true] : bool >-> Sortclass *)

(* ******************* *)
(* reflect に関する補題 *)
(* ******************* *)
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

(* ******************** *)
(* 2. bool に関する定理 *)
(* ******************** *)
(* 決定可能なbool値等式を定義する。 *)
Definition eqb (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

(* bool値等式とLeibniz同値関係の等価性を証明する。 *)
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

Definition bool_eqMixin := EqMixin bool_eqP.            (* @EqMixin bool eqb bool_eqP. *)
Definition bool_eqType := EqType bool_eqMixin.          (* @EqType bool bool_eqMixin. *)
Check @eq_op bool_eqType true true : bool.
Fail eq_op true true.
Fail Check true == true : bool.

Canonical Structure bool_eqType.            (* ここここ *)
(*
bool_eqType を EqType... の Canonical Structure としたことで、 
特に指定せずとも EqType.. の具体例として bool_eqType を使えるようになる。
bool値どうしの比較を、EqType 上の同値関係 (eq_op, ==) を使って行えるようになる。
see. http://mathink.net/program/coq_setoid.html

つまり、bool に対して、eq_op が使用可能になる。
 *)
Check true == true : bool.
Check eq_op true true : bool.

(*
まとめて、以下のように書ける。
Canonical Structure bool_eqType := EqType bool_eqMixin. (* @EqType bool bool_eqMixin. *)
*)

Print Canonical Projections.
(* bool <- sort ( bool_eqType ) *)

(* ******************** *)
(* 2'. nat に関する定理 *)
(* ******************** *)
(* 決定可能なbool値等式を定義する。 *)
Fixpoint eqn m n {struct m} :=
  match m, n with
  | 0, 0 => true
  | S m', S n' => eqn m' n'
  | _, _ => false
  end.

(* bool値等式とLeibniz同値関係の等価性を証明する。 *)
Lemma nat_eqP : axiom eqn.                  (* ssrnat.eqnP *)
Proof.
  intros n m.
  apply (iffP (idP (eqn n m))).
  (* eqn n m -> n = m *)
  - generalize dependent m.
    induction n; intros m.
    + now destruct m.
    + destruct m as [|m' IHm'].
      * now simpl.
      * simpl. intro H. f_equal.
        now apply IHn.
  (* n = m -> eqn n m *)
  - intros H.
    rewrite <- H.
    now elim n.
Qed.

Fail Check @eq_op nat_eqType 1 1.
Fail Check 1 == 1.

(* eqn と eq の違い。 *)
(* すでに [is_true] : bool >-> Sortclass のコアーションが有効なので、 *)
Check eqn : nat -> nat -> bool.
Check eqn : nat -> nat -> Prop.
Check eqn : rel nat.
Check eq : nat -> nat -> Prop.
Fail Check eq : nat -> nat -> bool.
Fail Check le : rel nat.

(* ここここ *)
Definition nat_eqMixin := EqMixin nat_eqP.              (* @EqMixin nat eqn nat_eqP. *)
Canonical Structure nat_eqType := EqType nat_eqMixin.   (* @EqType nat nat_eqMixin. *)
(*
nat_eqType を EqType... の Canonical Structure としたことで、 
特に指定せずとも EqType.. の具体例として nat_eqType を使えるようになる。
nat値どうしの比較を、EqType 上の同値関係 (eq_op, ==) を使って行えるようになる。
see. http://mathink.net/program/coq_setoid.html
*)
Print Canonical Projections.
(* nat <- sort ( nat_eqType ) *)

(* nat に対して、eq_op が使用可能になる。 *)
Check @eq_op nat_eqType 1 1 : bool.
Check 1 == 1 : bool.

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
Lemma bool_eqP' :
  forall {x y : bool}, reflect (x = y) (x == y).
Proof.
  now apply (@eqP bool_eqType).
  Undo 1.
  now apply bool_eqP.
(*
  intros x y.
  now case x; case y; constructor.
*)
(*
  now apply ReflectT.
  now apply ReflectF.
  now apply ReflectF.
  now apply ReflectT.
*)
Qed.

Check introT bool_eqP' : _ = _ -> _ == _.
Check elimT bool_eqP' : _ == _ -> _ = _.

Goal forall x y : bool, x == y -> x = y.
Proof.
  intros x y H.
  apply (elimT bool_eqP').                  (* apply/eqP *)
  (* Goal : true == true *)
  apply (introT bool_eqP').                 (* apply/eqP *)
  (* Goal : true = true *)
  apply (elimT bool_eqP').                  (* apply/eqP *)
  (* Goal : true == true *)
  now apply H.
Qed.

Lemma nat_eqP' :
  forall {x y : nat}, reflect (x = y) (x == y).
Proof.
  now apply (@eqP nat_eqType).
  Undo 1.
  now apply nat_eqP.
Qed.

Check introT nat_eqP' : _ = _ -> _ == _.
Check elimT nat_eqP' : _ == _ -> _ = _.

Goal forall n m : nat, n = m -> n == m.
Proof.
  intros n m H.
  apply (introT nat_eqP').                  (* apply/eqP *)
  (* Goal : 1 = 1 *)
  apply (elimT nat_eqP').                   (* apply/eqP *)
  (* Goal : 1 == 1 *)
  apply (introT nat_eqP').                  (* apply/eqP *)
  (* Goal : 1 = 1 *)
  now apply H.
Qed.

(* END *)
