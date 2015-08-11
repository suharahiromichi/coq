(**
スモール SSReflect の製作
======
2015/08/11

@suharahiromichi


# はじめに

CoqのSSReflect拡張（以下、SSReflect）は、熱心なユーザがいる一方、
「x = y と x == y の相互で変換は奇妙」として敬遠される場合があります。


今回は、SSReflectのしくみを理解することを目的に、
Starndard Coqをもとに「SSReflectもどき」を作ってみます。


それを通して、Coqのコアーション(coersion)などの
説明もしたいと思いますから、
SSReflectに興味のない人も聴いていただけるとうれしいです。


# 今回のソースの在処

- Markdown版は以下のソースから生成した。

``https://github.com/suharahiromichi/coq/tree/master/ssr/ssr_small_ssreflect.v``

- 以下の版で動作を確認した。SSReflectおよびMathCompは使わない。

``8.4pl2``


# ちょっと自己紹介

@suharahiromichi

1. プログラマ

2. 勤務先：アニメ「風たちぬ」のモデルの工場

3. 本来業務：システムインテグレーション（多言語プログラミング、ソースコード変換）
（品質保証やプログラム検証・証明は担当外）

4. アイコン：ボーイング737（多く売れた飛行機こそ名機）

# 概要

1. bool型からProp型へのコアーション
2. Reflect補題の証明
3. eqTypeの定義、eqType型からType型へのコアーション、eq_op(==)定義
4. bool型の値を引数とする決定可能なbool値等式の定義と、Leibniz同値関係の等価性
5. nat型の値を引数とする決定可能なbool値等式の定義と、Leibniz同値関係の等価性
6. Viewとその補題
7. x = y と x == y の相互変換の例

# 説明

## 準備
*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
以上の設定によって、引数の一部を省略することができる。
すべての引数を省略せず指定する場合は、関数などの前に ``@`` をつける。
*)

(**
## bool型からProp型（命題型）へのコアーション

bool型の値をProp型の値として扱えるようにする（埋め込むともいう）。
「is_true : bool -> Prop」という関数を、表記上、省略することで実現する。
*)

(**
bool型からProp型に変換する関数を定義する。
 *)
Definition is_true (x : bool) : Prop := x = true.
Check true : bool. 
Check is_true true : Prop.                  (* コアーションを使わない例 *)
Fail Check true : Prop.                     (* また、is_trueは省けない。 *)

(**
bool型からProp型へのコアーションを宣言する。
 *)
Coercion is_true : bool >-> Sortclass.      (* コアーションの宣言 *)
Print Graph.                                (* [is_true] : bool >-> Sortclass *)

(**
すると。。。
 *)
Check true : Prop.                          (* コアーションが使えるようになる。 *)

(*
## Reflect と Reflect補題

*)
Inductive reflect (P : Prop) : bool -> Set :=
| ReflectT :   P -> reflect P true
| ReflectF : ~ P -> reflect P false.

(**
Reflect補題を証明する。
あとでbool値等式がLeibniz同値関係が等価であることの説明に使う。
*)

(**
PとQが同値のとき：
*)
Lemma iffP : forall (P Q : Prop) (b : bool),
               reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Proof.
  intros P Q b HPb HPQ HQP.
  case HPb; intros HP.
  - apply ReflectT. auto.
  - apply ReflectF. auto.
Qed.

(**
reflect b b：

reflect (is_true b) b の is_true が省略されている。
*)
Lemma idP : forall b : bool, reflect b b.
Proof.
  intros b.
  case b.
  - now apply ReflectT.
  - now apply ReflectF.
Qed.

(**
## eqType型を定義する。
*)
Record mixin_of (T : Type) :=
  EqMixin {                                 (* Mixin *)
      op : T -> T -> bool;                  (* rel T でもよい。 *)
      axiom : forall x y : T, reflect (x = y) (op x y)
    }.

Record eqType :=                            (* type *)
  EqType {                                  (* Pack *)
      sort :> Type;                         (* eqType型 から Type型 へのコアーション *)
      m : mixin_of sort
    }.

Print Graph.                                (* コアーション *)
(* [sort] : type >-> Sortclass *)

Definition eq_op (T : eqType) := op (m T).
Check eq_op : forall T : eqType, (sort T) -> (sort T) -> bool. (* eqTypeからTypeへのコアーションを使わない例 *)
Check eq_op : forall T : eqType, T -> T -> bool.               (* eqTypeからTypeへのコアーションを使う例  *)
Notation "x == y" := (eq_op x y) (at level 70, no associativity).

(**
eq_op についての補題を証明しておく。
*)
Lemma eqP (T : eqType) : forall {x y : T}, reflect (x = y) (eq_op x y).
Proof.
  case T.
  intros sort m.
  now apply m.
Qed.

(**
## bool型
*)

(**
bool型を引数とする、決定可能なbool値等式を定義する。
 *)
Definition eqb (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

(**
bool値等式とLeibniz同値関係の等価性を証明する。
 *)
Lemma bool_eqP : forall x y, reflect (x = y) (eqb x y).
Proof.
  intros x y.
  apply (iffP (idP (eqb x y))).
  - unfold eqb.
    now case x; case y.
  - unfold eqb.
    now case x; case y.
Qed.

(**
eq と eqb の違い。
 *)
Check eq : bool -> bool -> Prop.
Check eqb : bool -> bool -> bool.

Fail Check eq : bool -> bool -> bool. (* これは当然 *)
Check eqb : bool -> bool -> Prop.     (* bool型からProp型へのコアーションが有効なため。 *)

(**
bool_eqTypeを定義する。

bool と eqb と bool_eqP から、コンストラクタ EqMixin と EqType で、
bool_eqTypeを作る。bool_eqType は、eqType型である。
 *)

Definition bool_eqMixin := @EqMixin bool eqb bool_eqP. (* EqMixin bool_eqP でもよい。 *)
Definition bool_eqType := @EqType bool bool_eqMixin.   (* EqType bool_eqMixin でもよい。 *)

Check true : sort bool_eqType.
Check true : bool_eqType.
Check @eq_op bool_eqType : (sort bool_eqType) -> (sort bool_eqType) -> bool.
Check @eq_op bool_eqType : bool -> bool -> bool.
Check @eq_op bool_eqType : bool_eqType -> bool_eqType -> bool.
Check @eq_op bool_eqType true true : bool.

Fail Check eq_op true true : bool.
Fail Check true == true : bool.


(**
eq_op (==) は、厳密には、``forall T : eqType, (sort T) -> (sort T) -> bool`` の型を持つ。
ここで、``forall T`` のT型の値を第0引数、``sort T``型の値を第1第2引数と呼ぶ。
第0引数は、通常はImplcit Argumentによって省略される(``==``なら必ず省略）。

第0引数Tを省略せずに、bool_eqType を書いた場合、
``sort T``はboolとなり、第1第2はbool型の値を書くことができる。
（例：``@eq_op bool_eqType true true``）。

しかし、第0引数を省略して、第1第2引数にtrueを書いた場合、
trueの型であるbool型から、eqType型の値であるbool_eqTypeを連想することはできない。

そこで、bool_eqTypeをeqType型の値として使えるようにすることで、
第1第2引数にbool型の値を書いたときに、第0引数にbool_eqTypeを書いたとみなせるようになる。

つまり、第0引数が省略できるようになる。
 *)

(**
bool_eqType をカノニカル宣言する。

これで、eqType型の具体例として bool_eqType型の値を使えるようになる。
*)
Canonical Structure bool_eqType.
Print Canonical Projections.                (* bool <- sort ( bool_eqType ) *)

(**
つまり、bool型の値に対して、``==`` が使用可能になる。
 *)
Check eq_op true true : bool.
Check true == true : bool.

(**
なお、まとめて以下のように書くこともできる。
``Canonical Structure bool_eqType := @EqType bool bool_eqMixin.``
*)

(**
## nat型
*)

(**
nat型を引数とする、決定可能なbool値等式を定義する。
 *)
Fixpoint eqn m n {struct m} :=
  match m, n with
  | 0, 0 => true
  | S m', S n' => eqn m' n'
  | _, _ => false
  end.

(**
bool値等式とLeibniz同値関係の等価性を証明する。
 *)
Lemma nat_eqP : forall x y, reflect (x = y) (eqn x y).
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

(**
eq と eqn の違い。
 *)

Check eq : nat -> nat -> Prop.
Check eqn : nat -> nat -> bool.

Fail Check eq : nat -> nat -> bool.   (* これは当然 *)
Check eqn : nat -> nat -> Prop.       (* bool型からProp型へのコアーションが有効なため。 *)

(**
nat_eqType型を定義する。
 *)

Definition nat_eqMixin := @EqMixin nat eqn nat_eqP.   (* EqMixin nat_eqP でもよい。 *)
Definition nat_eqType := @EqType nat nat_eqMixin.     (* EqType nat_eqMixin *)

Fail Check eq_op 1 1 : bool.
Fail Check 1 == 1 : bool.

(**
nat_eqType をカノニカル宣言する。

これで、eqType型の具体例として natl_eqType型の値を使えるようになる。
*)
Canonical Structure nat_eqType.
Print Canonical Projections.                (* nat <- sort ( nat_eqType ) *)

(**
つまり、nat型の値に対して、``==`` が使用可能になる。
 *)
Check eq_op 1 1 : bool.
Check 1 == 1 : bool.

(**
なお、まとめて以下のように書くこともできる。
``Canonical Structure nat_eqType := @EqType nat nat_eqMixin.``
*)

(**
## View

SSReflectでは、``apply/V`` のVをViewと呼ぶ。View Hintとして登録された、補題が自動的に補われる。
View Hintとして使われることの多い補題に``elimT``と``introT``がある。
それを証明しておく。
*)

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

(**
## x = y と x == y の相互変換
*)

(**
boolの場合
*)
Goal forall x y : bool, x == y -> x = y.
Proof.
  intros x y H.
  apply (elimT eqP).                        (* apply/eqP *)
  (* Goal : true == true *)
  apply (introT eqP).                       (* apply/eqP *)
  (* Goal : true = true *)
  apply (elimT eqP).                        (* apply/eqP *)
  (* Goal : true == true *)
  now apply H.
Qed.

Goal forall n m : nat, n = m -> n == m.
Proof.
  intros n m H.
  apply (introT eqP).                       (* apply/eqP *)
  (* Goal : 1 = 1 *)
  apply (elimT eqP).                        (* apply/eqP *)
  (* Goal : 1 == 1 *)
  apply (introT eqP).                       (* apply/eqP *)
  (* Goal : 1 = 1 *)
  now apply H.
Qed.

(**
# 参考文献

1. アフェルト レナルド 「定理証明支援系 Coq による形式検証」
https://staff.aist.go.jp/reynald.affeldt/ssrcoq/coq-kyoto2015.pdf

2. @suharahiromichi 「SSReflectのViewとView Hintについてのメモ」
http://qiita.com/suharahiromichi/items/02c7f42809f2d20ba11a
*)

(* END *)
