(**
MathComp の 空集合 について
======
2019/05/02

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_set0_notP.v

 *)

(**
OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

(**
# 説明

MathComp で、型 ``T : finType`` を全体集合とするとき、
型 ``T -> bool`` の関数、すなわち述語 ``p : pred T`` 
で決まる部分集合を考えます。

その部分集合が空集合、あるいは、濃度が0である場合、
述語 ``p`` は常に ``false`` を返すはずです。
それを証明してみます。

MathComp では、空集合は``set0``、集合の濃度は ``#|_|`` で表現します。
*)

(**
# コード例

## 空集合の場合についての証明

証明そのものはストレートですが、
setP や inE という、知らなければ使えない補題が必須になる例です。
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Test.

  Lemma set0_notPP (A : finType) (p : pred A) :
    [set x | p x] = set0 <-> (forall x, ~ p x).
  Proof.
    split.
    - move/setP => H x.
      move: (H x) => {H}.
      rewrite 2!inE.
        by move/idP.
      
    - move=> H.
      apply/setP => x.
      rewrite 2!inE.
        by apply/idP.
  Qed.

(**
setP は、ふたつの集合が等しいときにbool値のtrueを返す ``=i`` と、
Coq本来のProp型の等式 ``=`` が同値であるこを示します。
 *)
  
  Check setP : forall (T : finType) (A B : {set T}), A =i B <-> A = B.

(**
これをつかって、
``[set x | p x] = set0`` を ``[set x | p x] =i set0``
 に書き換えています。

このように書き換えると、x を適用する（前提の場合）、
または、x を introする（ゴールの場合）と
``(x \in [set x0 | p x0]) = (x \in set0)``
のように、``\in`` （∈) の表記に直すことができます。
*)

(**
一方、inE は、複雑で中をみてもよくわかりませんが、
``x \in [set x0 | p x0]`` を ``p x`` 
に書き換えます。

- ``\in`` の右は、述語 p （実際は A -> bool の関数）が true となる値の集合
- ``\in`` の左の ``x`` は、上記の要素

であるので、x について 述語 p が true となります。すなわち ``p x`` になるわけです。
 *)

(**
一方、空集合 ``set0`` は、``[set x0 | false]`` で定義されていますから、
``x \in set0`` は、単に ``false`` になります。
 *)

(**
``2!`` をつけることで、等式の左辺と右辺の両方に適用します。

最後は、``p x = false`` を idP を使って ``~ (p x)`` に変換することで、
証明か終わります。
 *)

  Check @idP : forall b1 : bool, reflect (b1 = true) b1.

(**
idP は、Prop型とbool型の間で（なにもしない）リフレクト補題ですが、
これを、前提に対して ``move/idP`` とviewとして使うことで、elimF が補われて、
前提の ``p x = false`` が ``~ p x`` となります。
 *)

  Check elimF idP : _ = false -> ~ _.

(**
同様に、ゴールの対して ``apply/idP`` とviewとして使うことで、introF が補われて、
ゴールの ``p x = false`` が ``~ p x`` となります。
 *)
  
  Check introF idP : ~ _ -> _ = false.


(**
## MathComp 風の補題

MathComp 風に、booelan の等式にした補題も証明してみます。
 *)

  Lemma set0_notPE (A : finType) (p : pred A) :
    ([set x | p x] == set0) = [forall x, ~~ p x].
  Proof.
    apply/idP/idP.
    - move/eqP => H.
      apply/forallP => x.
      apply/negP.
      move: x.
        by apply/set0_notPP.

    - move=> H.
      apply/eqP/set0_notPP.
      move/forallP in H.
      move=> x.
        by apply/negP.
  Qed.
  
(**
## 応用

上記の補題を使用して、別なな表記の場合についても証明しておきます。
 *)
  
  Lemma set0_notP' (A : finType) (p : pred A) :
    ([set x in p] == set0) = [forall x, ~~ p x].
  Proof.
      by apply: set0_notPE.
  Qed.

(**
   上記の構文糖です。
 *)
  
  Lemma set0_notP'' (A : finType) (p : pred A) :
    ([set x | x \in p] == set0) = [forall x, ~~ p x].
  Proof.
      by apply: set0_notPE.
  Qed.  


(**
## 濃度が0である場合についての証明    

空集合であることと濃度が0であることは同値ですが、それについても証明しておきます。
*)

  Lemma card0_notP (A : finType) (p : pred A) :
    (#|[set x in p]| == 0) = [forall x, ~~ p x].
  Proof.
    rewrite cards_eq0.
    apply: set0_notPE.
  Qed.


(**
## 補足

set0_notP' を直接証明する
*)

  Lemma p__inp (A : finType) (p : pred A) :
    (forall x : A, p x) <-> (forall x, (x \in p)).
  Proof.
    done.
  Qed.
  
  Lemma np__ninp (A : finType) (p : pred A) :
    (forall x : A, ~ p x) <-> (forall x, (x \in p) = false).
  Proof.
    split => H x; move: (H x) => {H} H.
    - apply: (@contraFF (x \in p) (p x)).
      + done.                               (* x \in p -> p x *)
      + by apply/negbTE/negP.
    - move/(@contraFN (p x) (x \in p)) in H.
      apply/negP/H.
      done.                                 (* p x -> x \in p *)
  Qed.
  
(**
# 最初に使った箇所

FRAP Map.v の MathComp への移植

https://github.com/suharahiromichi/coq/blob/master/frap/ssr_map.v
*)


(**
# 例題

option型を返す（部分）関数 m があるとします。
そのドメイン（Some _ を返す引数）の集合 dom を考えます。

このとき、
option型は、eqType とは限らないので、Some _ か None かどうかで true か false を決定する
関数 option_dec を用意しておきます。

関数 m のドメインが空集合である場合、m はすべての引数に対して None を返す
(option_dec が false) になることを証明します。
*)
  
  Definition fmap (A : finType) (B : Type) := A -> option B.

  Definition option_dec B (x : option B) :=
    match x with
    | Some _ => true
    | None => false
    end.
  
  Definition dom A B (m : fmap A B) : {set A} := [set x | option_dec (m x)].

  Lemma domE A B (m : fmap A B) :
    (dom m == set0) = ([forall k, option_dec (m k) == false]).
  Proof.
    apply/idP/idP => H.
    
    - apply/forallP => x.
      rewrite eqbF_neg.

      rewrite set0_notPE in H.
      move/forallP in H.
      move: (H x) => {H} H.
      done.
      
    - rewrite set0_notPE.
      apply/forallP => x.
      
      move/forallP in H.
      move: (H x) => {H} H.
      rewrite eqbF_neg in H.
      done.
  Qed.

End Test.

(* END *)
