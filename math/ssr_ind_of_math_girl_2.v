(**
数学ガールの「数学的帰納法」の問題
========================

@suharahiromichi

2020/06/21
 *)

(**
結城浩さんの「数学ガールの秘密ノート」に数学的帰納法の話題があります
（文献 [1][2]）。

数学ガールシリーズにしてはめずらしく、入試問題を題材にしています（文献 [3]）。
なので、解答にチャレンジしたかたもいるのではないかとおもいます。
これを ``Coq/MathComp`` （文献 [4]）で解いてみようと思います。

ひとつ前の値を使う数学的帰納法は、
Coqのような定理証明器（定理証明支援システム）が得意とすることのはずなのですが、
案外と大変でした。

- 与えられた漸化式をCoqの関数で定義しようとすると、停止性の証明が必要となる。

- 自然数をインデックスとする数列の一般項を求める問題だが、
数列の値は有理数（自然数を分母子とする分数）である。

- 一般項を求める過程で、有理数環の補題の証明が必要となる。

- その補題を適用するときに、分子が零ではないことを示す必要があり、
数列の項が ``> 0`` であることを（一般項を使わずに）証明する必要があった。
このとき、完全帰納法 (complete induction, strengthening induction) が必要になった。

- 高校数学なので、1からの自然数を使っているが、
Coqでは自然数は0以上としなければならない。


このファイルは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_ind_of_math_girl_2.v

証明スクリプトは模範回答ではなく、一例として参考程度にしてください。
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From common Require Import ssromega.        (* ssromega タクティク *)
Require Import Recdef.                      (* Function コマンド *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

Section Lemmas.
(**
# 補題

最初に、0でない(1を越える)有理数 p と q に対して、

$$ \frac{p}{\frac{p}{q}} = q $$


であることを証明します。分母を払うためのものですが、
この補題を ``Coq/MathComp`` のルールにしたがって、``divKq`` と命名します。
有理数(q)の割算(div)で、もとに戻る(K, cancel) の意味です。

ここで証明した補題の段階では、``0 < p`` と ``0 < q`` の前提が残ることに注意してください。

``divKq`` を直接証明してもよいのですが、
``divqA`` と ``mulKq`` の別の補題を証明して使っています。
その証明には、MathComp の環 (ring) の補題を使っています（文献 [6]）。
*)
  
  Lemma divqA (p q r : rat) : 0 < q -> 0 < r -> p / (q / r) = (p * r) / q.
  Proof.
    move=> Hq Hr.
    rewrite invrM.                 (* p * (r^-1^-1 / q) = p * r / q *)
    - rewrite invrK.               (* p * (r / q) = p * r / q *)
      rewrite -div1r.              (* p * (r * (1 / q)) = p * r * (1 / q) *)
        by rewrite !mulrA.
    - by apply: unitf_gt0.                 (* q \is a GRing.unit *)
    - rewrite -invr_gt0 in Hr.             (* r^-1 \is a GRing.unit *)
        by apply: unitf_gt0.
  Qed.
  
  Lemma mulKq (p q : rat) : 0 < p -> (p * q) / p = q.
  Proof.
    move=> Hp.
    rewrite [p * q]mulrC.                   (* q * p / p = q *)
    (* rewrite -div1r. *)
    rewrite -mulrA.                         (* q * (p / p) = q *)
    (* rewrite div1r. *)
    rewrite divrr.                          (* q * 1 = q *)
    - by rewrite mulr1.
    - by rewrite unitf_gt0.                 (* p \is a GRing.unit *)
  Qed.
  
  Lemma divKq (p q : rat) : 0 < p -> 0 < q -> p / (p / q) = q.
  Proof.
    move=> Hp Hq.
    rewrite divqA; last done; last done.
    rewrite mulKq; last done.
    done.
  Qed.

End Lemmas.

(**
# 試験問題

本題の試験問題（文献 [3]）を解いていきます。大筋では、数学ガール（文献 [1][2]）と同じです。
ですが、少し異なるとこともあります。

- 数列 a の漸化式を Coq の再帰関数として定義する。
ただし、a_0 を起点とするため、試験問題や数学ガールの記事と比べると、
インデックスがひとつづづずれる。

```math

a_0 = 3\\
a_1 = 3\\
a_2 = 3\\
a_{k+3} = \frac{a_k + a_{k+1}}{a_{k+2}}
```

- 数列 b と 数列 c を 数列 a から定義する。
ただし、試験問題や数学ガールの記事と逆に、
b_k を a_2k （偶数番）、c_k を a_2k+1 （奇数番）とする。

```math

b_k = a_{2k}\\
c_k = a_{2k+1}
```

- 試験問題（と数学ガールの記事）の誘導問題に従い、b_k+2 と c_k+1 の式を求める
(lemma_1 と lemma_2)。

- ``0 < a_k`` であることを証明する。このとき、
帰納法の仮定として、``k0 < k`` であるすべてのk0で ``0 < a_k0`` が成り立つものとして、
``0 < a_k`` であることを証明する（完全帰納法を使う）。

- ``0 < a_k`` から ``0 < b_k`` と ``0 < c_k`` を導く。

- b_k = b_k+1 であること(lemma_3)を、k についての数学的帰納法で証明する。
このとき、 補題 ``divKq`` を使う。
そして、``divKq`` の前提を消すために、a_k, b_k, c_k のそれぞれが ``> 0`` であることを使う。

- 最終的に、bの一般項 b_k が 3 であることを証明することは同じである。

$$ b_k = 3 $$
 *)

Section Question.

(**
## 数列 a_k の漸化式

数列 a_k の漸化式 を Coq の関数で定義します。
自然数 k を引数とする再帰関数として定義することになりますが、
Coq はこの関数が、任意の自然数 k に対して計算できること、
すなわち、再帰が止まって値が求まること（計算の停止性）を
自動判定できない、というエラーを出力します。

そこで、定義に際して、再帰の毎に k の値が減ることを明示してやります
（Function コマンドを使う。文献 [9]）。

すると、Function コマンドは、``k.+2 < k.+3`` と ``k.+1 < k.+3`` と ``k < k.+3``
を証明することを求めてきます（証明責務ですね）。
FunctionコマンドはStarndard Coqのコマンドなので、
StandardCoqの不等式 (例：``(k.+2 < k.+3)%coq_nat``) を出力します。
これは ``apply/ltP`` を使って、
MathCompの不等式（例：``(k.+2 < k.+3)%N``）に変換できます。
Coqの自然数 ``%coq_nat`` が MathCompの自然数 ``%N`` に変わっています。

そして、ssromega タクティク（文献 [7]）を使って証明します。
なお、ここでは文献[7]のうちの sssromega の定義の部分だけを取り出して、
最初に ``Require Import ssromega`` で読み込んでいます。
*)

  (* 【２】の式 (a_k の定義) *)
  Function a (k : nat) {measure id k} : rat :=
    match k with
    | 0 => ratz 3                           (* fracq (3%:Z, 1%:Z) *)
    | 1 => ratz 3                           (* fracq (3%:Z, 1%:Z) *)
    | 2 => ratz 3                           (* fracq (3%:Z, 1%:Z) *)
    | k'.+3 => (a k' + a k'.+1) / a k'.+2
  end.
  - move=> k3 k2 k1 k Hk1 Hk2 Hk3.
    apply/ltP.
      by ssromega.
  - move=> k3 k2 k1 k Hk1 Hk2 Hk3.
    apply/ltP.
      by ssromega.
  - move=> k3 k2 k1 k Hk1 Hk2 Hk3.
    apply/ltP.
      by ssromega.
  Defined.               (* 実際に計算できるように、Defined で終える。 *)

(**
関数をその定義で
展開するときには、``rewrite /a`` (Standard Coq の unfold タクティク)
は使用できず。a_equation による書き換えを使わなければいけません（文献 [9]）。

これは、Function コマンドで定義した関数 a には、
その定義に余計な証明が付随するからです。
*)

(**
## 数列 b_k と c_k

a_k の定義を使います。
*)  
  Definition b (k : nat) : rat := a k.*2.   (* a_k の偶数番 *)

  Definition c (k : nat) : rat := a k.*2.+1. (* a_k の奇数番 *)
  
(**
実際に計算してみます。正しそうですね。
*)
  Compute a 0.                              (* b_0 = 3 *)
  Compute a 1.                              (* c_0 = 3 *)
  Compute a 2.                              (* b_1 = 3 *)
  Compute a 3.                              (* c_1 = 2 *)
  Compute a 4.                              (* b_2 = 3 *)
  Compute a 5.                              (* c_2 = 5/3 *)
  Compute a 6.                              (* b_3 = 3 *)
  Compute a 7.                              (* c_3 = 14/9 *)

(**
## b_k+2 と c_k+1 の式

数学ガールの記事にあるとおり、
誘導問題に従い、b_k+2 と c_k+1 の式を求めます。

a_k の漸化式（の関数）の定義を展開するときは、a_equation を使っています。

補題 doubleS は ``2 * (n + 1)`` と ``2 * n + 2`` との間の書き換えをします。
*)

  Check doubleS : forall n : nat, (n.+1).*2 = n.*2.+2.
  
  Lemma lemma_1 (k : nat) :                 (* 計算で得た式(1) *)
    b k.+2 = (c k + b k.+1) / c k.+1.
  Proof.
    rewrite /b !doubleS a_equation.
    rewrite /c doubleS.
    done.
  Qed.
  
  Lemma lemma_2 (k : nat) :                 (* 計算で得た式(2) *)
    c k.+1 = (b k + c k) / b k.+1.
  Proof.
    rewrite /c !doubleS a_equation.
    rewrite /b doubleS.
    done.
  Qed.

(**
## ``0 < a_k`` の証明

- ``0 < a_k`` であることを証明するには、
a_k-1, a_k-2, a_k-3 の値が ``> 0`` であることが必要になります。

そこで、帰納法の仮定 ``k' < k`` の k' に対して ``a_k' < 0`` が成り立つとして、
``k' < k+1`` の k' に対して ``a_k' < 0`` が成り立つことを示す
完全帰納法 (complete induction) を使って証明します。

k についての完全帰納法を使うとき、MathComp の場合は、``elim: k {-2}k (leqnn k)``
というイデオムを使います
（文献 [8]、および、[5] の 3.2.4 Application: strengthening induction）。

- ``[| [| [| k']]]`` はパズルのようですが、a_k' の k' について条件分け（0か1以上か）
を3回繰り返すことで、a_k'+3 を取り出すためのものです。

- 補題 divr_gt0 と addr_gt0 を適用することで、``0 < (a k' + a k'.+1) / a k'.+2`` を
``0 < a k'`` と ``0 < a k'.+1`` と ``0 < a k'.+2`` に分解します。

- 最後に、それぞれに対して（完全）帰納法の仮定を適用することで得られた不等式は、ssromga
で片付けています。
*)
  Lemma ak_gt_0 k : 0 < a k.
  Proof.
    elim: k {-2}k (leqnn k) => [k | k IHk]. (* 完全帰納法のイデオム *)
    - by rewrite leqn0 => /eqP ->.
    - case=> [| [| [| k']]] Hk //. (* 条件分けで a k'+3 を取り出す。 *)
      rewrite a_equation.
      rewrite divr_gt0 //.
      + rewrite addr_gt0 //.
        * apply: IHk.
            by ssromega.
        * apply: IHk.
            by ssromega.
      + apply: IHk.
          by ssromega.
  Qed.

(**
##  ``0 < b_k`` と ``0 < c_k`` の証明

``0 < a_k`` を使います。
*)  
  Lemma bk_gt_0 k : 0 < b k.
  Proof.
    rewrite /b.
      by apply: ak_gt_0.
  Qed.
  
  Lemma ck_gt_0 k : 0 < c k.
  Proof.
    rewrite /c.
      by apply: ak_gt_0.
  Qed.

(**
## ``b_k = b_k+1``

k についての数学的帰納法を使い、
帰納法の仮定 ``b_k = b_k+1`` が成り立つとして、``b_k+1 = b_k+2`` を示すことで証明します。
先に証明した、lemma_1とlemma_2と、帰納法の仮定を使って書き換えることで得られた、
``b_k = (c_k + b_k) / ((c_k + b_k) / b_k)`` から、
divKq で書き換えることで、``(c_k + b_k)`` を消し（分母を払い）ます。

このとき分母 ``(c_k + b_k)`` が ``> 0`` である条件を示すために、前節の補題を使います。
*)  
  Lemma lemma_3 (k : nat) : b k = b k.+1.
  Proof.
    elim: k => [| k IHk] //.
    rewrite lemma_1.
    rewrite lemma_2.
    rewrite -[in RHS]IHk.
    rewrite -[in LHS]IHk.
    rewrite [b k + c k]addqC.
    rewrite [RHS]divKq; first by rewrite IHk.
    - apply: addr_gt0.
      + by apply: ck_gt_0.
      + by apply: bk_gt_0.
    - by apply: bk_gt_0.
  Qed.
  
(**
## 求めたかったもの : b_k の一般項 ``b_k = 3``
*)  
  Theorem bk_3 (k : nat) : b k = ratz 3.    (* b の一般項 *)
  Proof.
    elim: k => [| k IHk] //.
      by rewrite -lemma_3.
  Qed.
  
End Question.

(**
# 文献


[1] 結城浩、数学ガールの秘密ノート - センター試験の数学的帰納法、Cakes

- 第13回 (前編) https://cakes.mu/posts/1095

- 第14回 (後編) https://cakes.mu/posts/1157


[2] 結城浩、数学ガールの秘密ノート/整数で遊ぼう、SBクリエイティブ


[3] 2013年大学入試センター試験 数学II・数学B 第3問、

https://school.js88.com/sd_article/dai/dai_center_data/pdf/2013sugaku2B_q.pdf


[4] 萩原学 アフェルト・レナルド、「Coq/SSReflect/MathCompによる定理証明」、森北出版


[5] Mathematical Components Book、

https://math-comp.github.io/mcb/


[6] MathComp, ssralg.v,

https://github.com/math-comp/math-comp/blob/master/mathcomp/algebra/ssralg.v


[7] Affeldt Reynald, Library ssrnat_ext,

https://staff.aist.go.jp/reynald.affeldt/coqdev/ssrnat_ext.html


[8] Coq/SSReflectでたった1行のコマンドで完全帰納法を適用する方法

https://qiita.com/nekonibox/items/514da8edfc6107b57254


[9] Advanced recursive functions

https://coq.inria.fr/refman/language/gallina-extensions.html#advanced-recursive-functions
*)

(* END *)
