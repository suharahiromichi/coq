(**
スモール SSReflect の製作
======
2015/08/11

@suharahiromichi


# はじめに

CoqのSSReflect拡張（以下、SSReflect）は、熱心なユーザがいる一方、
「``x = y`` との ``x == y`` との間で勝手な変換ができることが判らない」
と言われることがあります。

今回は、SSReflectのしくみを理解することを目的に、
Starndard Coqをもとに「SSReflectもどき」を作り、
``x = y`` と ``x == y`` の相互変換、つまり、
Leibniz同値関係とbool値等式のリフレクションができるまでを示します。

それを通して、
Coqのコアーション(coersion)や、カノニカル・ストラクチャ(Canonical Structure)の
説明もしたいと思います。


# 今回のソースの在処

- Markdown版は以下のソースから生成した。
``https://github.com/suharahiromichi/coq/tree/master/ssr/ssr_small_ssreflect.v``

- 以下の版で動作を確認した。SSReflectおよびMathCompは使わない。
``8.4pl2``


# 概要

1. bool型からProp型へのコアーション
2. Reflect補題の証明
3. eqTypeの定義、eqType型からType型へのコアーション、eq_op (``==``)定義
4. bool型の値を引数とする決定可能なbool値等式の定義と、Leibniz同値関係の等価性
5. nat型の値を引数とする決定可能なbool値等式の定義と、Leibniz同値関係の等価性
6. Viewとその補題の証明
7. Leibniz同値関係とbool値等式のリフレクション（x = y と x == y の相互変換）の例

# 説明

## 準備
*)
Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.
Set Print All.
(* Set Printing Coercions. *)

(**
最初のふたつで引数の一部を省略できるようになる。
ただし、今回はこの設定の有無が影響しないように
関数等の``()``、``{}``や``@``を適切に使い分けている。
（``{}``は省略できる引数、``@``はそれを省略せず指定することを意味する）

``Set Printing Coercions`` は、コアーションを省略せずに表示するもの
であるが、``*goals*``や``*response*``バッファ にしか影響しない。
*)

(**
## bool型からProp型（命題型）へのコアーション

bool型からProp型に変換する関数を定義する。
 *)
Definition is_true (x : bool) : Prop := x = true.
Check is_true : bool -> Prop.
Check true : bool. 
Check is_true true : Prop.

(**
bool型の値をProp型の値として扱えるようにする（埋め込むともいう）。
これは、``is_true : bool -> Prop`` という関数を、表記上、省略することで実現する。
*)

Fail Check true : Prop.                     (* まだ、is_trueは省けない。 *)
(**
bool型からProp型へのコアーションを宣言する。
 *)
Coercion is_true : bool >-> Sortclass.      (* コアーションの宣言 *)
Print Graph.                                (* [is_true] : bool >-> Sortclass *)
(**
すると。。。
 *)
Check true : Prop.                          (* コアーションが使えるようになる。 *)
(**
もし、``Set Printing Coercions`` を指定した
場合は、``*response*``バッファには省略されたis_trueが補われ
て、``is_true true : Prop`` と表示される。
 *)

(**
## Reflect と Reflect補題

``reflect P b`` は、命題Pとbool値bが等価であることを示す。
*)
Inductive reflect (P : Prop) : bool -> Set :=
| ReflectT :   P -> reflect P true
| ReflectF : ~ P -> reflect P false.

(**
ふたつのReflect補題を証明しておく。
あとでbool値等式がLeibniz同値関係が等価であることの説明に使う。
*)

(**
### 補題 iffP

``P<->Q`` のとき、``reflect P b`` なら ``reflect Q b``。

証明の概要：

- ``reflect P true``  で、``P->Q``   なら、``reflect Q true``
- ``reflect P false`` で、``~P->~Q`` なら、``reflect Q false``
- ``P->Q`` だけではだめで、``Q->P`` が必要になる。
*)
Lemma iffP : forall {P Q : Prop} {b : bool},
               reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Proof.
  intros P Q b HPb HPQ HQP.
  case HPb; intros HP.
  - apply ReflectT. auto.
  - apply ReflectF. auto.
Qed.

(**
### 補題 idP

``reflect (is_true b) b`` は、成立する。

コアーションを使って、``forall b : bool, reflect b b`` と書いてもよい。
*)
Lemma idP : forall {b : bool}, reflect (is_true b) b.
Proof.
  intros b.
  case b.
  - now apply ReflectT.
  - now apply ReflectF.
Qed.

(**
## eqType型

bool値等式が定義された型を導入する。
*)
Record mixin_of (T : Type) :=
  EqMixin {
      op : T -> T -> bool;                         (* opはbool値等式 *)
      a : forall x y : T, reflect (x = y) (op x y) (* opはLeibniz同値関係と等価であること *)
    }.

Record eqType :=
  EqType {
      sort : Type;                          (* 補足1参照 *)
      m : mixin_of sort
    }.
Check sort : eqType -> Type.

(**
実際に使うために、eq_op (``==``) を定義する。
*)
Definition eq_op {T : eqType} := @op (sort T) (m T).
Notation "x == y" := (eq_op x y) (at level 70, no associativity).

Check eq_op : (sort _) -> (sort _) -> bool.
(**
eq_op は3つの引数を取るが、``{}``で囲んだ最初の引数Tはimplicitになる。
``==`` のときもTは省略される。
 *)

Check @eq_op : forall T : eqType, (sort T) -> (sort T) -> bool.
(**
しかし、``@eq_op``とすると、引数Tを指定したり、Checkで見ることができる。
 *)

(**
### 補題 eqP

eq_op は Leibniz同値関係と等価であるという補題を証明しておく。この補題は最後に使う。
*)
Lemma eqP : forall {T : eqType} {x y : sort T}, reflect (x = y) (@eq_op T x y).
Proof.
  intro T.
  case T.
  intros sort m.
  now apply m.
Qed.

(**
## bool型の例
*)

(**
bool型を引数とする、決定可能なbool値等式を定義する。
 *)
Definition eqb (x y : bool) : bool :=
  match x, y with
    | true,  true  => true
    | true,  false => false
    | false, true  => false
    | false, false => true
  end.

(**
bool値等式とLeibniz同値関係の等価性を証明する。
 *)
Lemma bool_eqP : forall (x y : bool), reflect (x = y) (eqb x y).
Proof.
  intros x y.
  apply (iffP idP).
  - now case x; case y.                     (* eqb x y -> x = y *)
  - now case x; case y.                     (* x = y -> eqb x y *)
Qed.

(**
eq と eqb の違い。
 *)
Check eq : bool -> bool -> Prop.      (* Leibniz同値関係 *)
Check eqb : bool -> bool -> bool.     (* bool値等式 *)
Check eqb : bool -> bool -> Prop.     (* bool型からProp型へのコアーションが有効なため。 *)

(**
bool_eqTypeを定義する。

コンストラクタ EqMixin と EqType で、bool と eqb と bool_eqP から、
bool_eqTypeを作る。bool_eqType は eqType型である。
 *)
Definition bool_eqMixin := @EqMixin bool eqb bool_eqP. (* EqMixin bool_eqP でもよい。 *)
Definition bool_eqType := @EqType bool bool_eqMixin.   (* EqType bool_eqMixin でもよい。 *)

Fail Check eq_op true true : bool.          (* ！？ *)
Fail Check true == true : bool.             (* ！？ *)

(**
eq_op にbool型の値が書けない！？


説明：

eq_op (``==``) は、次の型を持つ。
*)
Check @eq_op : forall T : eqType, sort T -> sort T -> bool.
(**
最初の引数を省略せずに、bool_eqType と書いた場合、
*)
Check @eq_op bool_eqType : (sort bool_eqType) -> (sort bool_eqType) -> bool.
(**
``sort bool_eqType`` は bool であるから、
*)
Check @eq_op bool_eqType : bool -> bool -> bool.
(**
以降の引数にはbool型の値を直接書くことができる。
*)
Check @eq_op bool_eqType true true : bool.
(**
しかし、最初の引数``T:=bool_eqType``省略して、以降の引数にtrueを書いた場合、
*)
Fail Check eq_op true true.
(**
``Error: The term "true" has type "bool" while it is expected to have type "sort ?241"``

最初の引数がbool_eqTypeであることが判らないのでエラーになる。指定していないから判らない。
eqType型であることは判っても、そのインスタンスをすべてチェックするわけにはいかない
（インスタンスの一覧表はない）ため。
 *)

(**
そこで、Canonical Structureコマンドによって、
bool_eqTypeをeqType型の値として引数の推論に使うよう、登録する。
このときbool_eqTypeはeqTypeのCanonical Instanceまたは、単にCanonicalと呼ぶ。

ひとたび、最初の引数が``T:=bool_eqType``であると判れば、
（省略しないときと同様に）``sort bool_eqType`` は bool なので、以降の引数にbool型の値を書くことができる。
*)

(**
以上を箇条書きにすると：
1. 最初の引数を省略したeq_opまたは ``==`` に、bool型の値を書いた場合において。
2. eqTypeのカノニカルインスタンスとしてbool_eqTypeが登録されているので、それが見つけられる。
3. eq_opの最初の引数が``T:=bool_eqType``であるとする。
4. eq_opの定義から、以降の引数は、``sort bool_eqType``型 であることになる。
5. ``sort bool_eqType`` は bool である。
6. 以降の引数にbool型の値を書くことが許されるようになる。

つまり、

bool_eqTypeをカノニカルにすると、
省略された最初の引数は、bool_eqType であると推論できるので、
最初の引数を省略したeq_opまたは ``==`` にbool型の値を書いてもよい。
*)

(**
説明（終わり）
*)

(**
Canonical Structureコマンドを使って、bool_eqType を eqTypeのCanonical Instanceにする。
*)
Canonical Structure bool_eqType.            (* 補足2 *)
Print Canonical Projections.                (* bool <- sort ( bool_eqType ) *)

(**
すると。。。

bool型の値に対して、``==`` が使用可能になる。
（eq_opの最初の引数 ``T:=bool_eqType`` が省略できるようになる。）
 *)
Check eq_op true true : bool.
Check true == true : bool.

(**
蛇足：コアーションは、表記上で、型を変換する関数を省略できることである。
一方、カノニカル・ストラクチャーは、省略された引数を推論するためのヒントを登録することである。
*)

(**
## nat型の例
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
Lemma nat_eqP : forall (x y : nat), reflect (x = y) (eqn x y).
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

(**
eq と eqn の違い。
 *)
Check eq : nat -> nat -> Prop.        (* Leibniz同値関係 *)
Check eqn : nat -> nat -> bool.       (* bool値等式 *)
Check eqn : nat -> nat -> Prop.       (* bool型からProp型へのコアーションが有効なため。 *)

(**
nat_eqTypeを定義する。
 *)

Definition nat_eqMixin := @EqMixin nat eqn nat_eqP.   (* EqMixin nat_eqP でもよい。 *)
Definition nat_eqType := @EqType nat nat_eqMixin.     (* EqType nat_eqMixin *)

Fail Check eq_op 1 1 : bool.
Fail Check 1 == 1 : bool.

(**
Canonical Structureコマンドを使って、nat_eqType を eqTypeのCanonical Instanceにする。
*)
Canonical Structure nat_eqType.
Print Canonical Projections.                (* nat <- sort ( nat_eqType ) *)

(**
すると。。。

nat型の値に対して、``==`` が使用可能になる。
（eq_opの最初の引数 ``T:=nat_eqType`` が省略できるようになる。）
 *)
Check eq_op 1 1 : bool.
Check 1 == 1 : bool.

(**
## View

SSReflectでは、``apply/V`` と書くことができ、そのVをViewと呼ぶ。
Viewのみapplyするのではなく、View Hintとして登録された補題が自動的に補われる（場合がある）。

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
## Leibniz同値関係とbool値等式のリフレクション（x = y と x == y の相互変換）の例

SSReflectでは、ゴールが``x = y``のとき、``apply/eqP``を実行することで``x == y``に変換される。
このとき、View Hintとして、elimT が使われる。すなわち、``apply (elimT eqP)`` である。

また、ゴールが``x == y``のとき、おなじく``apply/eqP``を実行することで``x = y``に変換される。
このとき、View Hintとして、introT が使われる。すなわち、``apply (introT eqP)`` である。
*)

(**
boolの場合
*)
Goal forall x y : bool, x == y -> x = y.
Proof.
  intros x y H.
  apply (elimT eqP).                        (* apply/eqP *)
  (* Goal : x == y *)
  apply (introT eqP).                       (* apply/eqP *)
  (* Goal : x = y *)
  apply (elimT eqP).                        (* apply/eqP *)
  (* Goal : x == y *)
  now apply H.
Qed.

(**
natの場合
*)
Goal forall n m : nat, n = m -> n == m.
Proof.
  intros n m H.
  apply (introT eqP).                       (* apply/eqP *)
  (* Goal : n = m *)
  apply (elimT eqP).                        (* apply/eqP *)
  (* Goal : n == m *)
  apply (introT eqP).                       (* apply/eqP *)
  (* Goal : n = m *)
  now apply H.
Qed.

(**
# まとめ

1. 「SSReflectもどき」をつくってみた

2. SSReflect で、Leibniz同値関係 (``x = y``) と bool値等式 (``x == y``) が相互に変換できるのは、
両者が等価であることが、それぞれの型で、証明されているから (bool_eqTypeやnat_eqType)。

3. 上記を実現するために、Coqのコアーション(coersion)や
カノニカル・ストラクチャCanonical Structure)を利用する。
*)

(**
# 補足1

EqType の ``sort : Type`` を ``sort :> Type`` とすることによって、
eqTypeからTypeへのコアーションを有効にできる。
``[sort] : eqType >-> Sortclass``

これによって、``Lemma eqP (T : eqType) : forall {x y : sort T},...``
のsortを省略して、`Lemma eqP (T : eqType) : forall {x y : T},...``と表記できる。

また、eq_op が、
``Check @eq_op bool_eqType : bool_eqType -> bool_eqType -> bool.``
と見えるようになる。

しかし、これはカノニカルによる引数の推論とは全く別のことである。
今回は、それを強調するために、eqTypeのsortによるコアーションを指定しないようにし、
sortによるeqTypeからTypeへの変換は、すべて明示的に指定することにした。
*)

(**
# 補足2

DefinitionとCanonical Structureコマンドをまとめて、
以下のように書くこともできる。

- ``Canonical Structure bool_eqType := @EqType bool bool_eqMixin.``
- ``Canonical Structure nat_eqType := @EqType nat nat_eqMixin.``

SSReflectでは、単にCanonicalである。
*)

(**
# 参考文献

1. アフェルト レナルド 「定理証明支援系 Coq による形式検証」
``https://staff.aist.go.jp/reynald.affeldt/ssrcoq/coq-kyoto2015.pdf``

2. Assia Mahboubi, Enrico Tassi, "Canonical Structures for the working Coq user"
``https://hal.inria.fr/hal-00816703v1/document``

The essence of the Canonical Structures mechanism is to extend the unification algorithm
of the Coq system with a database of hints. (p.3)

2. @suharahiromichi, 「SSReflectのViewとView Hintについてのメモ」
``http://qiita.com/suharahiromichi/items/02c7f42809f2d20ba11a``
*)

(* END *)
