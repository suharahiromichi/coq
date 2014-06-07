Require Import ssreflect ssrbool eqtype ssrnat.

(**
# 第8回

http://qnighy.github.io/coqex2014/ex6.html

## 課題37 (別解）

自然数の対の商集合として整数を定義する。下の証明の空欄を埋めよ。
omega等を使ってもよい。

オリジナルの出題は SetoidClass を使用しているが、それを使わない場合。
「Add Setoid int equiv eq_int_equiv as ISetoid」を使う。

参考：
http://d.hatena.ne.jp/m-a-o/20110112
http://sssslide.com/www.slideshare.net/tmiya/coq-setoid-20110129
*)

Require Import Setoid.                      (* !!! *)

Record int :=
  {
    Ifst : nat;
    Isnd : nat
  }.

Lemma addn2r p m n : (m + p = n + p) -> (m = n).
Proof.
  move/eqP => H.
  apply/eqP.
  by rewrite -(eqn_add2r p).
Qed.

Definition equiv (x y : int) :=             (* == *)
  Ifst x + Isnd y = Ifst y + Isnd x.

Lemma eq_int_equiv : Setoid_Theory int equiv.
Proof.
  rewrite /Setoid_Theory.
  apply Build_Equivalence.
  by rewrite /Reflexive.
  by rewrite /Symmetric.
  rewrite /Transitive.
  move=> x y z.
  move=> Hxy Hyz.
  apply (addn2r (Ifst y + Isnd y)).
  rewrite !addnA.
  rewrite [Ifst x + Isnd z + Ifst y + Isnd y]addnC.
  rewrite [Ifst z + Isnd x + Ifst y + Isnd y]addnC.
  rewrite !addnA.
  rewrite [Isnd y + Ifst x]addnC.
  rewrite [Isnd y + Ifst z]addnC.
  rewrite Hxy.
  rewrite -Hyz.
  rewrite [Ifst y + Isnd z + Isnd x + Ifst y]addnC.
  rewrite [Ifst y + Isnd z + Isnd x]addnC.
  rewrite [Ifst y + Isnd z]addnC.
  rewrite !addnA.
  by [].
Qed.

Definition zero : int :=
  {|
    Ifst := 0;
    Isnd := 0
  |}.

Definition int_minus (x y : int) : int :=
  {|
    Ifst := Ifst x + Isnd y;
    Isnd := Isnd x + Ifst y
  |}.

Add Setoid int equiv eq_int_equiv as ISetoid.

Notation "x == z" := (equiv x z) (at level 70).

Lemma int_sub_diag : forall x, int_minus x x == zero.
Proof.
  move=> x.
  rewrite /equiv.
  rewrite /int_minus.
  by rewrite addn0 add0n addnC.
Qed.

(* まず、int_minus_compatを証明せずに、下の2つの証明を実行して、どちらも失敗することを確認せよ。*)
(* 次に、int_minus_compatを証明し、下の2つの証明を実行せよ。 *)

Add Parametric Morphism : int_minus with
  signature (equiv ==> equiv ==> equiv) as int_minus_compat.
Proof.
  move=> x y Hxy x' y' Hx'y'.
  rewrite /int_minus /equiv /=.

  have Hxy2 : (Ifst x + Isnd y = Ifst y + Isnd x) by apply Hxy.
  have Hx'y'2 : (Ifst x' + Isnd y' = Ifst y' + Isnd x') by apply Hx'y'.
  
  rewrite 2!addnA.
  rewrite [Ifst x + Isnd x' + Isnd y]addnC.
  rewrite [Ifst y + Isnd y' + Isnd x]addnC.
  rewrite 2!addnA.
  rewrite [Isnd y + Ifst x]addnC.
  rewrite -addnA.
  rewrite [Isnd x' + Ifst y']addnC.
  rewrite [Isnd x + Ifst y]addnC.
  rewrite -Hx'y'2.
  rewrite -Hxy2.
  rewrite -[(Ifst x + Isnd y) + Isnd y' + Ifst x']addnA.
  rewrite [Isnd y' + Ifst x']addnC.
  by [].
Qed.

(* rewrite と setoid_rewrite は SetoidClassと同様に使える。 *)

Goal forall x y, int_minus x (int_minus y y) == int_minus x zero.
Proof.
  intros x y.
  rewrite int_sub_diag.
  reflexivity.
Qed.

Goal forall x y, int_minus x (int_minus y y) == int_minus x zero.
Proof.
  intros x y.
  setoid_rewrite int_sub_diag.
  reflexivity.
Qed.

(**

おまけ : ISetoidの定義においてProgram InstanceをInstanceに変更し、Next Obligation. を取り除
いてもISetoidは定義できるが、続きがうまくいかなくなる。これは何故か？

ヒント

通常のイコール (Coq.Init.Logic.eq) 以外の同値関係を入れたい場合、Setoidを使います。Setoidに
よる書き換えは、通常rewriteで行えます。明示的にSetoidを使う場合は、setoid_rewriteを使います。

Setoidによってreplaceを行いたい場合はsetoid_replaceを使えます。通常のイコールと違い、
Setoidの同値関係を保存しない写像が存在する可能性があります。例えば、この問題におけるIfst関
数はSetoidの同値関係を保存しません。Setoidによる書き換えを行うためには、それぞれの関数が同
値関係を保存することを逐一証明する必要があります。

Recordは単一のコンストラクタを持ち再帰的でない型を定義するのに使えるコマンドです。メンバを
取り出す関数(この例ではIfst, Isnd)が自動的に定義されることや、{| ... |} という構文でRecord
型の値を記述できるという利点があります。
*)

(* END *)
