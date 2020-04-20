(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.2 eqtype.v --- eqType型のためのライブラリ

======

2018_11_17 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/eqtype.v
*)

(**
# eqType 型クラス （テンプレート）

eqType型クラスのインスタンス型 string_eqType を作る：
 *)

(*
(* String.v での定義を使う。 *)
Require Import String.
Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.
 *)

(* csm_4_1_ssrbool.v での定義を使う。 *)
Require Import String csm_4_1_ssrbool.
Definition string_eqMixin := @EqMixin string string_eqb string_eqP.
Canonical string_eqType := EqType string string_eqMixin.

(**
# generic theory (ジェネリックな定理)

eqType に対して使える定理
 *)

(**
## eqE （== を Equality.op に書き換える補題）
eq_op (==) に適用するという意味では、ジェネリックである。
 *)
Check @eqE nat_eqType 1 : eq_op 1 = Equality.op (Equality.class nat_eqType) 1.
(* ほとんど使わないだろう。 *)
Check eqbE.                                 (* eqb 専用 *)
Check eqnE.                                 (* eqn 専用 *)

(**
## eqP (= と == に間を変換する)
eq_op (==) に適用するという意味では、ジェネリックである。
 *)
(* これはよく使う。 *)
Check @eqP : forall (T : eqType) (x y : T), reflect (x = y) (x == y).
Check eqbP.                                 (* eqb 専用 *)
Check eqnP.                                 (* eqn 専用 *)

Lemma test : forall (x y : nat), x == y -> x + y == y + y.
Proof.
  move=> x y.
  move/eqP.                                 (* 前提部分 : x = y *)
  move=> <-.
  apply/eqP.                                (* 帰結部分 : x = y *)
  done.
Qed.

Lemma test4 : forall (n m : nat), if n == m then true else true.
Proof. move=> n m.
       case: eqP => H.                      (* ifP でもよい。 *)
       (* H : n = m *)
       + done.
       + done.
Qed.

(**
## eq_refl と eq_sym (== の 反射性と対称性の補題)
 *)
Check eq_refl : forall (T : eqType) (x : T), x == x.
Check eq_sym  : forall (T : eqType) (x y : T), (x == y) = (y == x).

(**
## 関数拡張 (f x == f y) = (x = y) が成立する。

ただし、前提によって補題が異なる。
 *)
Print injective.         (* f x1 = f x2 -> x1 = x2 *)
Check inj_eq : forall (aT rT : eqType) (f : aT -> rT),
    injective f ->                          (* 単射 *)
    forall x y : aT, (f x == f y) = (x == y).

Print cancel.            (* g (f x) = x *)
Check can_eq : forall (aT rT : eqType) (f : aT -> rT) (g : rT -> aT),
    cancel f g ->                           (* fのキャンセルgが存在 *)
    forall x y : aT, (f x == f y) = (x == y).
(* f自体が自己キャンセルである必要はない。 *)

Print bijective.         (* cancel f g -> cancel g f -> bijective f *)
Check bij_eq : forall (aT rT : eqType) (f : aT -> rT),
    bijective f ->                          (* 全単射 *)
    forall x y : aT, (f x == f y) = (x == y).

(* ちなみに、単射の逆は必ず成り立つことに、注意してください。 *)
Check f_equal.           (* x = y -> f x = f y *)


(**
## contraXX (== に関する対偶)

直観主義論理では、一般に対偶は成り立たないが、否定の側がboolなら成立する。
最後のふたつを覚えておけばよいかも。
 *)
Check contraTeq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x != y -> ~~ b) -> b -> x = y.
Check contraNeq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x != y -> b) -> ~~ b -> x = y.
Check contraFeq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x != y -> b) -> b = false -> x = y.
Check contraTneq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x = y -> ~~ b) -> b -> x != y.
Check contraNneq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x = y -> b) -> ~~ b -> x != y.
Check contraFneq : forall (T1 : eqType) (b : bool) (x y : T1),
    (x = y -> b) -> b = false -> x != y.
Check contra_eqN : forall (T1 : eqType) (b : bool) (x y : T1),
    (b -> x != y) -> x = y -> ~~ b.
Check contra_eqF : forall (T1 : eqType) (b : bool) (x y : T1),
    (b -> x != y) -> x = y -> b = false.
Check contra_eqT : forall (T1 : eqType) (b : bool) (x y : T1),
    (~~ b -> x != y) -> x = y -> b.

Check contra_eq : forall (T1 T2 : eqType) (z1 z2 : T2) (x1 x2 : T1),
       (x1 != x2 -> z1 != z2) -> z1 = z2 -> x1 = x2.
Check contra_neq : forall (T1 T2 : eqType) (z1 z2 : T2) (x1 x2 : T1),
       (x1 = x2 -> z1 = z2) -> z1 != z2 -> x1 != x2.

(**
## eq_irrelevance

https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_axiom_free.v
 *)
Check eq_irrelevance  : forall (T : eqType) (x y : T) (e1 e2 : x = y), e1 = e2.


(**
# injective や、 cancel、pcancel から eqType を定義する：

以下では、nat との injective と pcancel (部分キャンセル) を使う。 

'I_n との canel を使う例（bool と のcanelを使う場合も同様である)。
https://github.com/suharahiromichi/coq/blob/master/math-comp-book/suhara.ch7-windrose-2.v
*)

Inductive balle :=
| rouge  (* red ball, la balle rouge, 紅玉 *)
| blanc. (* white ball, la balle blanc, 白玉 *)

Fail Compute rouge == blanc.                (* == が定義されていない。 *)

Definition balle2nat (b : balle) : nat :=
  match b with
  | rouge => 1
  | blanc => 0
  end.

Definition nat2balle (b : nat) : option balle :=
  match b with
  | 1 => Some rouge
  | 0 => Some blanc
  | _ => None
  end.

(* balle2nat の単射性をつかってballe_eqTypeを定義する。 *)
Lemma inj_b2n : injective balle2nat.
Proof. by case; case. Qed.

Definition balle_eqMixin := InjEqMixin inj_b2n.
Canonical balle_eqType := EqType balle balle_eqMixin.

Compute rouge == blanc.                     (* == が定義される。 *)
Compute eq_op rouge blanc.
Print Canonical Projections.
(* balle <- Equality.sort ( balle_eqType ) *)
Compute @eq_op balle_eqType rouge blanc. (* カノニカルプロジェクションが使われている。 *)

(* balle2nat と nat2balle が逆であることをつかってballe_eqTypeを定義する。 *)
Lemma pcan_b2n : pcancel balle2nat nat2balle.
Proof. by case. Qed.

Definition balle_eqMixin' := PcanEqMixin pcan_b2n.
Canonical balle_eqType' := EqType balle balle_eqMixin'.
(* この場合も、inj_b2n の場合と同様に、== が定義される。 *)

(*
bool の equal (balle_eqb) を定義し、
eqTypeの公理を満たすインスタンスとして balle_eqType を定義する。
*)
Definition balle_eqb (x y : balle) : bool :=
  match (x, y) with
  | (rouge, rouge) => true
  | (blanc, blanc) => true
  | _ => false
  end.

Lemma balle_eqb_spec x y : reflect (x = y) (balle_eqb x y).
Proof. apply: (iffP idP); by case: x; case y. Qed.

Definition balle_eqMixin'' := EqMixin balle_eqb_spec.
Canonical balle_eqType'' := EqType balle balle_eqMixin''.
(* この場合も、inj_b2n の場合と同様に、== が定義される。 *)

(**
# eqType型のインスタンス
 *)

(**
## unit_eqType
 *)

(**
## bool_eqType
 *)

(**
## unit_eqType
 *)

(**
## prod_eqType (直積型)
 *)

(**
## option_eqType
 *)

(**
## tag_eqType
 *)

(**
## sum_eqType
 *)

(**
## その他

nat_eqType      nat.v
seq_eqType      seq.v
tree_eqType     choice.v
ordinal_eqType  fintype.v
*)

(**
# ジェネリックな型としての eqType

Type の代わりに eqType とすると、eqType型である型の値どうしは「==」の成り立つようになる。
 *)
Section GenType.

(**
## Type型の型T の変数 x と y
 *)
  Variable T : Type.
  Variables x y : T.
  
  Check x = y.
  Fail Check x == y.                        (** == が成り立たない。 *)

(**
## Type型の型Tの seq の変数 s と t
 *)
  Variables s t : seq T.

  Check s = t.
  Fail Check s == t.                        (** == が成り立たない。 *)

(**
## eqType型の型T の変数 m と n
 *)
  Variable eT : eqType.
  Variables m n : eT.

  Check m = n.
  Check m == n.                             (** == が成り立つ。 *)
  
(**
## eqType型の型eTの seq の変数 u と v
 *)
  Variables u v : seq eT.

  Check u = v.
  Check u == v.                             (** == が成り立たつ。 *)

End GenType.

(**
## 自分で定義した関数
*)

Definition testT (T : Type) (x : T)  : T := x.
Definition testeT (eT : eqType) (m : eT)  : eT := m.

(**
Type型の型Tには、任意の型が代入できる。
*)
Check bool : Type.
Compute @testT bool true.                   (* true *)

Check nat : Type.
Compute @testT nat 1.                       (* 1 *)

Check seq nat : Type.
Compute @testT (seq nat) [:: 1].            (* [:: 1] *)

(**
同様に、eqType型eTには、任意のeqType型（eqType型の型インスタンス）が代入できる。
また、内部で、以下のコアーションが効くため、eqType型の型の値として、natの値が書ける。
*)
Compute Equality.sort nat_eqType.           (* nat *)
Check true : bool_eqType.
Check 1 : nat_eqType.
Check [:: 1] : seq_eqType nat_eqType.

Check bool_eqType : eqType.
Compute @testeT bool_eqType true.

Check nat_eqType : eqType.
Compute @testeT nat_eqType 1.

Check seq_eqType nat_eqType : eqType.
Compute @testeT (seq_eqType nat_eqType) [:: 1].

(**
nat は、nat_eqType のカノニカル解であるため、上記の nat_eqType型であるべき箇所に書ける。
省略された eqType型の第１引数 nat_eqType を nat型の値「1」から見つけることができる。
*)
Compute testeT true.
Compute testeT 1.
Compute testeT [:: 1].

Compute testeT true : bool.
Compute testeT 1 : nat.
Compute testeT [:: 1] : seq nat.

(**
コアーションとカノニカル解のメカニズムを追うのは難しいが、
Type の代わりに eqType とすると、eqType型である型の値どうしは「==」の成り立つようになる、
と覚えておいてもよい。
*)


(* ************************** *)
(* モチベーション維持のために  *)
(* ************************** *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

(* 
eqTypeが重要なのは、MathCompのクラス階層の起点であるから。

rat             pair
   ←サブタイプ         ←インスタンス
                ↑カノニカル
rat_Ring                                ringType
rat_ZmodType                            zmodType
rat_countType   pair_countType                  countType
rat_choiceType  pair_choiceType         choiceType
rat_eqType      pair_eqType             eqType
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(* ssralg.v *)
Import GRing.Theory.                 (* mulrNN を使えるようにする。 *)
(* ssrnum.v *)
Import Num.Theory.                   (* normr0_eq0 などを使えるようにする。 *)
(* ssrint.v *)
Import intZmod.                        (* addz など *)
Import intRing.                        (* mulz など *)
Import intOrdered.                     (* lez など *)
(* Open Scope int_scope. *)
(* Open Scope rat_scope. *)
Open Scope ring_scope.

(* # 有理数型 *)

Definition q1_3 := fracq (1%:Z, 3%:Z).
Definition q2_6 := fracq (2%:Z, 6%:Z).

Compute (valq q2_6).1.                      (* 1 *)
Compute (valq q2_6).2.                      (* 3 *)

Compute q1_3 == q2_6.                       (* true *)

Goal q1_3 = q2_6.
Proof.
  Fail reflexivity.
    by apply/eqP.
Qed.


(* ## 有理数における (−a)(−b) = ab *)

Check rat_Ring : ringType.               (* rat_RingType ではない。 *)
Lemma rat_mulrNN (q1 q2 : rat) : - q1 * - q2 = q1 * q2.
Proof.
    by apply mulrNN.
Qed.


(* # 多項式型 *)

(* ## 多項式における (−a)(−b) = ab *)

Check polynomial_ringType rat_Ring : ringType.
Lemma poly_mulrNN' (p1 p2 : polynomial rat_Ring) : - p1 * - p2 = p1 * p2.
Proof.
    by apply mulrNN.
Qed.

(* Phantom Type ファントムタイプ *)

Lemma poly_mulrNN (p1 p2 : {poly rat}) : - p1 * - p2 = p1 * p2.
Proof.
    by apply mulrNN.
Qed.

(* {poly R} は phantom type を使い、R を ringTypeのカノニカル型に制限することを意味する。

see. https://github.com/suharahiromichi/coq/blob/master/math-comp-book/suhara.ch7-phantom_types.v
 *)

(* {poly R} は poly_of の構文糖衣であることが判る。 *)
Set Printing All.
Check {poly rat}.
Check @poly_of _        (Phant rat).        (* 構文糖を展開する。 *)
Check @poly_of rat_Ring (Phant rat). (* カノニカルプロジェクションで、引数を補完した。 *)
(* このカノニカルプロジェクションをおこなうために、
   poly_of には、後述する（使われない）二つ目の引数 a : phant R がある。 *)

(* Phant が出てくるが、これは普通にインダクティブに定義されている。 *)
Print phant.
(*
Variant phant (p : Type) : Prop := Phant : phant p

Coqの基本的な書き方に修正すると：

Inductive phant : Type -> Prop :=
| Phant p : phant p.

コンストラクタとしては難しくない。
*)
Check Phant rat : phant rat.                (* ここに省略はない。 *)

(* poly_of は R に加えて、使われない a という引数をとる。 *)
Print poly_of.
(* poly_of (R : ringType) (a : phant R) := polynomial R.
   phant の引数は Type なので、コアーションが機能する。
   poly_of (R : ringType) (a : phant (GRing.Ring.sort R)) := polynomial R. *)

(* poly_of の定義から、
   a の型は ``phant rat_Ring`` であるけれど、コアーションを考慮すると、 
   a の型は ``phant rat`` でよいことになる。
 *)
Check Phant rat : phant rat_Ring.           (* コアーションあり *)
Check Phant rat : phant (GRing.Ring.sort rat_Ring). (* 省略なし。 *)
Check Phant rat : phant rat.                        (* 省略なし。 *)


(* このことは、カノニカルプロジェクションの意味では、「==」と同じで、 *)
Check true : bool.
(*           ^^^^ *)
Check true == true.
Check @eq_op bool_eqType true true.
(*           ^^^^^^^^^^^ *)
(* と *)
Check Phant rat : phant rat.
(*                      ^^^ *)
Check @poly_of rat_Ring (Phant rat).
(*             ^^^^^^^^ *)
(* の類似で納得できるだろうか。 *)


(* ## 多項式の計算例： *)

Definition p2 : {poly rat} := \poly_(i < 3) fracq (i%:Z, 2%:Z).
(* (2/2)x^2 + (1/2)x + (0/2) *)

Definition p3 : {poly rat} := \poly_(i < 2) fracq (i%:Z, 3%:Z).
(* (1/3)x + (0/3) *)

Check - p2 * - p3 : {poly rat}.
Check - p2 * - p3 : polynomial rat_Ring.
(* Compute すると、終わらない。 *)

(* END *)
