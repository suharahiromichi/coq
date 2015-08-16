(**
SSREFLECt もどきを作ってみる。

@suharahiromichi

2015_05_13

2015_06_28

2015_07_29
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Module SmallSSR.
(* *************** *)
(* 0. コアーション *)
(* *************** *)
Definition is_true (x : bool) : Prop := x = true.
Check is_true true : Prop.                  (* boolのコアーションを使わない例 *)
Fail Check true : Prop.                     (* boolのコアーションを使う例。まだエラーになる。 *)
Coercion is_true : bool >-> Sortclass.      (* bool から Prop へのコアーション*)
Check true : Prop.                          (* boolのコアーションを使う。 *)

Print Graph.                           (* コアーションの印刷 *)
(* [is_true] : bool >-> Sortclass *)


(* **************** *)
(* 1. Reflect      *)
(* **************** *)
Inductive reflect (P : Prop) : bool -> Set :=
| ReflectT :   P -> reflect P true
| ReflectF : ~ P -> reflect P false.

(*
Definition rel (T : Type) := T -> T -> bool.
Check rel : Type -> Type.
*)

(* 変な名前だが、あとで証明する。 *)
Definition axiom (T : Type) (e : T -> T -> bool) := (* e : rel T *)
  forall x y : T, reflect (x = y) (e x y).
Check axiom : forall T : Type, (T -> T -> bool) -> Type.

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

Lemma idP : forall {b : bool}, reflect b b. (* reflect (is_true b) b. *)
Proof.
  intros b.
  case b.
  - now apply ReflectT.
  - now apply ReflectF.
Qed.

(* **************** *)
(* 1. eqType の準備 *)
(* ***************** *)
Record mixin_of (T : Type) :=
  EqMixin {                                 (* Mixin *)
      op : T -> T -> bool;                  (* rel T でもよい。 *)
      a : axiom op
    }.

Record eqType :=                            (* type *)
  EqType {                                  (* Pack *)
      sort :> Type;                         (* eqType から Type へのコアーション *)
      m : mixin_of sort
    }.

Print Graph.                                (* コアーション *)
(* [sort] : type >-> Sortclass *)

Definition eq_op (T : eqType) := op (m T).
Check eq_op : forall T : eqType, (sort T) -> (sort T) -> bool. (* eqTypeのコアーションを使わない例 *)
Check eq_op : forall T : eqType, T -> T -> bool.   (* eqTypeのコアーションを使う例  *)
(* rel T  *)
Notation "x == y" := (eq_op x y) (at level 70, no associativity).

(* 補題：使わない *)
Lemma eqP (T : eqType) : axiom (@eq_op T).
Proof.
  unfold axiom.
  case T.
  intros sort m.
  now apply m.
Qed.
Check eqP : forall T : eqType, axiom (@eq_op T).


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
  apply (iffP idP).                         (* (iffP (@idP (eqb x y))) *)
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
(* Check eqb : rel bool. *)
Check eq : bool -> bool -> Prop.
Fail Check eq : bool -> bool -> bool.
(* Fail Check le : rel bool. *)

Definition bool_eqMixin := EqMixin bool_eqP.            (* @EqMixin bool eqb bool_eqP. *)
Definition bool_eqType := EqType bool_eqMixin.          (* @EqType bool bool_eqMixin. *)
Check @eq_op bool_eqType true true : bool.
Fail Check eq_op true true : bool.
Fail Check true == true : bool.

Canonical Structure bool_eqType.            (* ここここ *)
(*
bool_eqType を EqType... の Canonical Structure としたことで、 
特に指定せずとも EqType.. の具体例として bool_eqType を使えるようになる。
bool値どうしの比較を、EqType 上の同値関係 (eq_op, ==) を使って行えるようになる。
see. http://mathink.net/program/coq_setoid.html

つまり、bool に対して、eq_op が使用可能になる。
 *)
Check eq_op true true.
Check true == true : bool.

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
  apply (iffP idP).
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
(* Check eqn : rel nat. *)
Check eq : nat -> nat -> Prop.
Fail Check eq : nat -> nat -> bool.
(* Fail Check le : rel nat. *)

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


End SmallSSR.

(* ここから SSReflect *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

(* 
任意の型XXXに対して、
SSReflectの機能を使って、同様のことを行う場合は、
決定可能なbool値等式を定義し、それとLeibniz同値関係の等価性を証明する。
そして、カノニカル・ストラクチャとして、XXX_eqTypeを定義する。
 *)

Module MyBool.

Inductive BOOL : Set :=
| TRUE : BOOL
| FALSE : BOOL.

(* ******************** *)
(* A. BOOL に関する定理 *)
(* ******************** *)
(* 決定可能なbool値等式を定義する。 *)
Definition eqB (b1 b2 : BOOL) : bool :=
  match b1, b2 with
    | TRUE, TRUE => true
    | TRUE, FALSE => false
    | FALSE, TRUE => false
    | FALSE, FALSE => true
  end.

(* bool値等式とLeibniz同値関係の等価性を証明する。 *)
Lemma BOOL_eqP (x y : BOOL) : reflect (x = y) (eqB x y).
Proof.
  by apply (iffP idP); case x; case y.
Qed.

Definition BOOL_eqMixin := EqMixin BOOL_eqP.
Canonical BOOL_eqType := EqType BOOL BOOL_eqMixin.

Check eq_op TRUE TRUE : bool.
Check TRUE == TRUE : bool.

Goal forall x y : BOOL, x == y -> x = y.
Proof.
  move=> x y H.
  apply/eqP.
  (* Goal : x == y *)
  apply/eqP.
  (* Goal : x = y *)
  apply/eqP.
  (* Goal : x == y *)
  by apply H.
Qed.

(* SSReflect の定義を使っている。 *)
About iffP.                                 (* Ssreflect.ssrbool.iffP *)
About idP.                                  (* Ssreflect.ssrbool.idP *)
About EqMixin.                              (* Ssreflect.eqtype.Equality.Exports.EqMixin *)
About EqType.                               (* Ssreflect.eqtype.Equality.Exports.EqType *)

End MyBool.

Module UpDown.

Inductive UpDown :=
| down
| up.

(* ******************** *)
(* A. UpDown に関する定理 *)
(* ******************** *)
Definition eqUD (b1 b2 : UpDown) : bool :=
  match b1, b2 with
    | up, up => true
    | up, down => false
    | down, up => false
    | down, down => true
  end.

(* bool値等式とLeibniz同値関係の等価性を証明する。 *)
Lemma updown_eqP (x y : UpDown) : reflect (x = y) (eqUD x y).
Proof.
  by apply (iffP idP); case x; case y.
Qed.

Definition updown_eqMixin := EqMixin updown_eqP.
Canonical updown_eqType := EqType UpDown updown_eqMixin.

Check eq_op up up : bool.
Check up == up : bool.

Goal forall x y : UpDown, x == y -> x = y.
Proof.
  move=> x y H.
  apply/eqP.
  (* Goal : x == y *)
  apply/eqP.
  (* Goal : x = y *)
  apply/eqP.
  (* Goal : x == y *)
  by apply H.
Qed.

(* SSReflect の定義を使っている。 *)
About iffP.                                 (* Ssreflect.ssrbool.iffP *)
About idP.                                  (* Ssreflect.ssrbool.idP *)
About EqMixin.                              (* Ssreflect.eqtype.Equality.Exports.EqMixin *)
About EqType.                               (* Ssreflect.eqtype.Equality.Exports.EqType *)

End MyBool.


(* ******************** *)
(* B. なぜ == を使うのか *)
(* ******************** *)

(* == を使うことで、証明が簡単になる例 *)
Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof.
  by elim: p.                               (* ワンライナー *)
Qed.

Goal forall p m n, (p + m = p + n) -> (m = n).
Proof.
  move=> p m n.
  move/eqP => H.
  apply/eqP.
    (* ここで、p + m == p + n -> m == n になる。 *)
  by rewrite -(eqn_add2l p m n).
Qed.

Goal forall p m n, (p + m = p + n) -> (m = n).
Proof.
  intros p m n H.
  induction p.
  - now rewrite !add0n in H. 
  - admit.
Qed.


Lemma eqn_add2l' : forall p m n, (p + m = p + n) = (m = n).
Proof.
  intros p m n.
  induction p.
  admit.
  admit.
Qed.

(* END *)
