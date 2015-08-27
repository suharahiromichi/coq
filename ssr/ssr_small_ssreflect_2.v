(**
スモール SSReflect の製作
======
2015/08/11
2015/08/16

@suharahiromichi


# はじめに

命題(Prop型)をbool型の式に変換すること（とその逆）をリフレクションと呼びます。

例： ``x = y`` と ``x == y``

命題をbool型の計算に変換することで、命題の証明が簡単になる場合があります。
そのリフレクションを「狭い範囲」で行い、証明の効率化を図るのが、
CoqのSmall Scale Reflection (SSReflect) 拡張です。

今回は、SSReflectのしくみを理解することを目的に、
Starndard Coqで「SSReflectもどき」を作り、
Leibniz同値関係とbool値等式のリフレクションができるまでを示します。

それを通して、
Coqのコアーション(coersion)や、カノニカル・ストラクチャ(Canonical Structure)の
説明もしたいと思います。


# 今回のソースの在処

- Markdown版は以下のソースから生成した。
``https://github.com/suharahiromichi/coq/tree/master/ssr/ssr_small_ssreflect_2.v``

- 以下の版で動作を確認した。
``8.4pl3``


# 概要

## 説明の流れ

1. bool型からProp型へのコアーションを定義する。
2. Reflect補題の証明する。iffP、idP。
3. eqType型クラスの定義と、eq_op (``==``) の定義、補題eqPの証明をする。
4. 決定可能なbool値等式とLeibniz同値関係の等価性の証明する。
5. eqTypeのインスタンスを定義する。
6. Viewとその補題の証明する。elimT、introT。
7. Leibniz同値関係とbool値等式のリフレクション（x = y と x == y の相互変換）の例
*)

(**
## updown型

このうち、4.と5.と7.は、等式の両辺の型ごとにおこなう必要がある。
ここでは、UP(up),OFF(off),DOWN(dn)の三値をとるupdown型を例とする。
*)

(**
updown型を定義する。
 *)
Inductive updown : Set :=
| up
| off
| dn.

(**
updown型を引数とする、決定可能なbool値等式を定義する。
*)
Definition eqUD (x y : updown) : bool :=
  match x, y with
    | up,  up  => true
    | off, off => true
    | dn,  dn  => true
    | _,   _   => false
  end.

(**
# 説明

## 準備
*)
Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.
Set Print All.
(* Set Printing Coercions. *)

Module SmallSSR.                            (* Small SSReflect *)
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
あとでbool値等式がLeibniz同値関係が等価であることの証明に使う。
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
## eqType型クラス

bool値等式が定義され、それと Leibniz同値関係の等価性が証明された型のクラスである。
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
Lemma eqP : forall {T : eqType} {x y : sort T},
              reflect (x = y) (@eq_op T x y).
Proof.
  intro T.
  case T.
  intros sort m.
  now apply m.
Qed.

(**
## updown型の例
*)

(**
### bool値等式とLeibniz同値関係の等価性を証明する。
 *)
Lemma updown_eqP : forall (x y : updown), reflect (x = y) (eqUD x y).
Proof.
  intros x y.
  (* apply (iffP idP); now case x; case y. *)
  apply (iffP idP).
  - now case x; case y.                     (* eqUD x y -> x = y *)
  - now case x; case y.                     (* x = y -> eqUD x y *)
Qed.

(**
eq と eqUD の違い。
 *)
Check eq   : updown -> updown -> Prop.    (* Leibniz同値関係 *)
Check eqUD : updown -> updown -> bool.    (* bool値等式 *)
Check eqUD : updown -> updown -> Prop.    (* bool型からProp型へのコアーションが有効なため。 *)

(**
### updown_eqType型を定義する。

eqType型クラスからupdown_eqType型を作る。
 *)
Definition updown_eqMixin := @EqMixin updown eqUD updown_eqP.
Definition updown_eqType := @EqType updown updown_eqMixin.

Fail Check eq_op up up : bool.          (* ！？ *)
Fail Check up == up : bool.             (* ！？ *)

(**
eq_op にupdown型の値が書けない！？

以下に説明する。

eq_op (``==``) は、次の型を持つ。
*)
Check @eq_op : forall T : eqType, sort T -> sort T -> bool.
(**
最初の引数を省略せずに、updown_eqType と書いた場合、
*)
Check @eq_op updown_eqType : (sort updown_eqType) -> (sort updown_eqType) -> bool.
(**
``sort updown_eqType`` は updown であるから、
*)
Check @eq_op updown_eqType : updown -> updown -> bool.
(**
以降の引数にはupdown型の値を直接書くことができる。
*)
Check @eq_op updown_eqType up up : bool.
(**
しかし、最初の引数``T:=updown_eqType``省略して、以降の引数にtrueを書いた場合、
*)
Fail Check eq_op up up.
(**
``Error: The term "up" has type "updown" while it is expected to have type "sort ?241"``

最初の引数がupdown_eqTypeであることが判らないのでエラーになる。指定していないから判らない。
eqType型であることは判っても、そのインスタンスをすべてチェックするわけにはいかない
（インスタンスの一覧表はない）ため。
 *)

(**
そこで、Canonical Structureコマンドによって、
updown_eqTypeをeqType型の値として引数の推論に使うよう、登録する。
このときupdown_eqTypeはeqTypeのCanonical Instanceまたは、単にCanonicalと呼ぶ。

ひとたび、最初の引数が``T:=updown_eqType``であると判れば、
（省略しないときと同様に）``sort updown_eqType`` は updown なので、以降の引数にupdown型の値を書くことができる。
*)

(**
つまり、

updown_eqTypeをカノニカルにすると、
省略された最初の（eqType型の）引数は、updown_eqType であると推論できるので、
最初の引数を省略したeq_opまたは ``==`` にupdown型の値を書いてもよい。
*)

(**
説明終わり。
*)

(**
Canonical Structureコマンドを使って、updown_eqType を eqTypeのCanonical Instanceにする。
*)
Canonical Structure updown_eqType.            (* 補足2 *)
Print Canonical Projections.                  (* updown <- sort ( updown_eqType ) *)

(**
すると。。。

updown型の値に対して、``==`` が使用可能になる。
（eq_opの最初の引数 ``T:=updown_eqType`` が省略できるようになる。）
 *)
Check eq_op up up : bool.
Check up == up : bool.

(* 念のため。 *)
Check up : updown.
Check up : sort updown_eqType.

(**
蛇足：コアーションは、表記上で、型を変換する関数を省略できることである。
一方、カノニカル・ストラクチャーは、省略された引数を推論するためのヒントを登録することである。
*)

(**
## Viewとその補題

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

(* ゴールに適用する例 *)
Goal forall x y : updown, x == y -> x = y.
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

(* 前提Hに適用する例 *)
Goal forall x y : updown, x == y -> x = y.
Proof.
  intros x y H.
  Check (elimT eqP H) : x = y.
  rewrite (elimT eqP H).
  Undo 1.
  apply (elimT eqP) in H.
  rewrite H.
  reflexivity.
Qed.

(**
# 補足1

EqType の ``sort : Type`` を ``sort :> Type`` とすることによって、
eqTypeからTypeへのコアーションを有効にできる。

``[sort] : eqType >-> Sortclass``

これによって、

``Lemma eqP (T : eqType) : forall {x y : sort T},...``

のsortを省略して、

``Lemma eqP (T : eqType) : forall {x y : T},...``

と表記できる。また、eq_op が、

``Check @eq_op updown_eqType : updown_eqType -> updown_eqType -> bool.``

と見えるようになる。

しかし、これはカノニカルによる引数の推論とは全く別のことである。
今回は、それを強調するために、eqTypeのsortによるコアーションを指定しないようにし、
sortによるeqTypeからTypeへの変換は、すべて明示的に指定することにした。
*)

(**
# 補足2

DefinitionとCanonical Structureコマンドをまとめて、以下のように書くこともできる。

``Canonical Structure updown_eqType := @EqType updown bool_eqMixin.``

また、SSReflectの場合は、次のようになる。

``Canonical updown_eqType := @EqType updown bool_eqMixin.``

いずれの場合も、(@を書かないことで）EqTypeの第1引数を省略することができる。
*)

(**
# 補足3

updown型の代わりにnat型でおこなうと、以下のようになる。
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
nat_eqType型を定義する。
 *)
Definition nat_eqMixin := @EqMixin nat eqn nat_eqP. (* EqMixin nat_eqP でもよい。 *)
Canonical Structure nat_eqType := @EqType nat nat_eqMixin. (* EqType nat_eqMixin *)
Print Canonical Projections.                (* nat <- sort ( nat_eqType ) *)

(**
nat型の値に対して、``==`` が使用可能になる。
（eq_opの最初の引数 ``T:=nat_eqType`` が省略できるようになる。）
 *)
Check eq_op 1 1 : bool.
Check 1 == 1 : bool.

(**
この補題は、bool値等式なので、
計算で（つまり、unfold と simpl と rewrite で）証明できる。
 *)
Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof.
  induction p as [|p IHp].
  - simpl. reflexivity.
  - unfold eq_op in *. simpl in *.
    rewrite IHp. reflexivity.
  Restart.
  induction p; auto.
Qed.

(**
リフレクションで（introTやeqPなどの補題を使う）、
bool値等式に変換して証明する。
 *)
Goal forall p m n, (p + m = p + n) -> (m = n).
Proof.
  intros p m n H.
  apply (introT eqP) in H.
  apply (elimT eqP).
  rewrite <- (eqn_add2l p m n).
  auto.
Qed.

End SmallSSR.                            (* Small SSReflect *)

(**
# SSReflectの機能を使う

（SSReflectをインストールしていない場合は、ここから最後までをコメントアウトしてください）

## updown型の例

スモール SSReflect で定義したupdown_eqType型を本物のSSReflectで定義してみる。
eqType型クラスは、SSReflectの``eqtype.v``で定義されているものを使う。
*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Lemma updown_eqP (x y : updown) : reflect (x = y) (eqUD x y).
Proof.
  by apply (iffP idP); case x; case y.
Qed.
Definition updown_eqMixin := EqMixin updown_eqP.
Canonical updown_eqType := EqType updown updown_eqMixin.

(**
SSReflectにおいて、自分で定義した型に対して、
Leibniz同値関係とbool値等式のリフレクションをするには、
以上の定義（等価性の証明と、型の定義）だけをすればよい。
 *)

Goal forall x y : updown, x == y -> x = y.
Proof.
  move=> x y H.
  apply/eqP.                                (* apply (elimT eqP) *)
  (* Goal : x == y *)
  apply/eqP.                                (* apply (introT eqP) *)
  (* Goal : x = y *)
  apply/eqP.                                (* apply (elimT eqP) *)
  (* Goal : x == y *)
  by apply H.
Qed.

(**
## bool値等式を使うと証明が易しくなる例

最後に、bool値等式を使うと証明が易しくなる例を示す。
*)

Lemma eqn_add2l (p m n : nat) : (p + m == p + n) = (m == n).
Proof.
  by elim: p.                               (* ワンライナー *)
Qed.

Goal forall (p m n : nat), (p + m = p + n) -> (m = n).
Proof.
  move=> p m n.
  move/eqP => H.                            (* H : p + m == p + n *)
  apply/eqP.                                (* Goal : m == n *)
  by rewrite -(eqn_add2l p m n).
Qed.


(**
# まとめ

1. 「SSReflectもどき」をつくってみた。

2. xxx_eqType型を作るときに、Leibniz同値関係(x = y) 
と、bool値等式(x == y)が等価であることを証明する必要がある。

3. 「==」を使うために、
カノニカル（カノニカル・ストラクチャCanonical Structure)が必要になる。
*)

(**
# 参考文献

1. アフェルト レナルド 「定理証明支援系 Coq による形式検証」
https://staff.aist.go.jp/reynald.affeldt/ssrcoq/coq-kyoto2015.pdf

2. Assia Mahboubi, Enrico Tassi, "Canonical Structures for the working Coq user"
https://hal.inria.fr/hal-00816703v1/document

The essence of the Canonical Structures mechanism is to extend the unification algorithm
of the Coq system with a database of hints. (p.3)

2. @suharahiromichi, 「SSReflectのViewとView Hintについてのメモ」
http://qiita.com/suharahiromichi/items/02c7f42809f2d20ba11a
*)

(* END *)
