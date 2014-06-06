Require Import ssreflect ssrbool eqtype ssrnat.

(**
# 第8回

http://qnighy.github.io/coqex2014/ex6.html

## 課題37 (種別:A / 締め切り : 2014/06/01)

自然数の対の商集合として整数を定義する。下の証明の空欄を埋めよ。
omega等を使ってもよい。
*)
Require Import SetoidClass.

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

Program Instance ISetoid : Setoid int :=
  {|
    equiv x y :=                            (* == *)
      Ifst x + Isnd y = Ifst y + Isnd x
  |}.
Next Obligation.
Proof.
  (* http://d.hatena.ne.jp/m-a-o/20110112 *)
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

Definition int_plus (x y : int) : int :=
  {|
    Ifst := Ifst x + Ifst y;
    Isnd := Isnd x + Isnd y
  |}.

Definition int_minus (x y : int) : int :=
  {|
    Ifst := Ifst x + Isnd y;
    Isnd := Isnd x + Ifst y
  |}.

Lemma int_sub_diag : forall x, int_minus x x == zero.
Proof.
  move=> x.
  by rewrite /= addn0 add0n addnC.
Qed.

Instance int_plus_compat :
  Proper (equiv ==> equiv ==> equiv) int_plus.
Proof.
  unfold Proper.
  unfold respectful.                        (* ==> *)
  move=> x y Hxy x' y' Hx'y'.
  rewrite /int_plus /=.

  have Hxy2 : (Ifst x + Isnd y = Ifst y + Isnd x) by apply Hxy.
  have Hx'y'2 : (Ifst x' + Isnd y' = Ifst y' + Isnd x') by apply Hx'y'.
  
  rewrite 2!addnA.
  rewrite -[Ifst x + Ifst x' + Isnd y]addnA.
  rewrite [Ifst x' + Isnd y]addnC.
  rewrite addnA.
  rewrite Hxy2.  
  rewrite -[(Ifst y + Isnd x) + Ifst x' + Isnd y']addnA.
  rewrite Hx'y'2.
  rewrite addnA.
  rewrite -[Ifst y + Isnd x + Ifst y']addnA.
  rewrite [Isnd x + Ifst y']addnC.
  rewrite addnA.
  by [].
Qed.

Instance int_minus_compat :
  Proper (equiv ==> equiv ==> equiv) int_minus.
Proof.
  unfold Proper.
  unfold respectful.                        (* ==> *)
  move=> x y Hxy x' y' Hx'y'.
  rewrite /int_minus /=.

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
