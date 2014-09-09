(**
日本ソフトウェア科学会
チュートリアル(1) 定理証明支援系Coq入門

講師：アフェルト レナルド 先生
https://staff.aist.go.jp/reynald.affeldt/ssrcoq/coq-jssst2014.pdf
 *)

(**
首記の講演から興味のもとに抜粋し、例題を追加したものです。
内容の責任は  @suharahiromichi にあります。
 *)

(**
eqtype.v: 決定可能な同値関係
 *)
Require Import ssreflect ssrfun ssrbool.

(** nat を定義する。 *)
Inductive nat : Set :=
| O
| S of nat.

(** 同値関係が決定可能なら, ブール値等式として定義ができる *)
Fixpoint eqn (m  n : nat) {struct m} : bool :=
  match m, n with
    | O, O => true
    | S m', S n' => eqn m' n'
    | _, _ => false
  end.

(**
eqType を使わない場合（普通はこれをしない）
eqtype_sample.v
 *)
Lemma myeqnP n m : eqn n m = true -> n = m.
Proof.
    by elim: n m => [|n IHn] [|m] //= /IHn ->.
Qed.

Record myeq := Eqtype {
  car : Set ; 
  myequality : car -> car -> bool ;
  Heq : forall x y : car, myequality x y = true -> x = y }.
Notation "a '===' b" := (myequality _ a b) (at level 70).

Check S O = S O.
Fail Compute S O === S O.                   (* まだ===は使えない。 *)
Canonical Structure eqtypenat := Eqtype _ _ myeqnP.
Compute S O === S O.                        (* true *)

Check (O : car _).
Check Heq.

(** 証明 *)
Goal forall n m : nat, n === m -> n = m.
Proof.
  move=> n m.
  move/myeqnP.
  Undo 1.
  move/Heq.
  by [].
Qed.

(**
eqType を使う場合
 *)
Require Import eqtype. (* eqtypeまで *)

Check S O = S O.
Fail Check S O == S O.

(** そのブール値等式と Leibniz 同値関係の等価性が証明をする。 *)
(* ここでは、<-> ではなく reflect を使う。 *)
Lemma eqnP : Equality.axiom eqn.            (*  reflect (x = y) (eqn x y) *)
Proof.
  move=> n m; apply: (iffP idP) => [|<-]; last by elim n.
    by elim: n m => [|n IHn] [|m] //= /IHn ->.
Qed.

(** その型はeqType として登録できる。 *)
Check S O = S O.
Fail Check S O == S O.
Canonical nat_eqMixin := EqMixin eqnP.
Canonical nat_eqType := Eval hnf in EqType nat nat_eqMixin.
Check S O == S O.

(** 証明 *)
Goal forall n m : nat, n == m <-> n = m.
Proof.
  move=> n m.
  by split; move/eqnP.
Qed.
(** ssrnat のおまけ *)
Lemma eqnE : eqn = eq_op. Proof. by []. Qed.
Lemma eqSS m n : (S m == S n) = (m == n). Proof. by []. Qed.
Lemma nat_irrelevance (x y : nat) (E E' : x = y) : E = E'.
Proof. exact: eq_irrelevance. Qed.

(**
より簡単だが、同じこと。
eqtype_sample.v のおまけ。
 *)
Structure myeq' := Myeq {
  car' : Set ;                              (* carrier *)
  myequality' : car' -> car' -> bool }.
Notation "a '===' b" := (myequality' _ a b) (at level 70).

Fail Check (true === false).
(* eqb : bool -> bool -> bool *)
Canonical Structure myeq_bool := Myeq bool eqb.
Check (true === false).
Eval compute in (true === false).

Fail Check (O === O).
(* eqn : nat -> nat -> bool *)
Canonical Structure myeq_nat := Myeq nat eqn.
Check (S O === S O).
Eval compute in (S O === S O).

(* END *)
