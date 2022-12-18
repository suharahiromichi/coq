(**
論理としてのProlog - Coqとの関係
========================

@suharahiromichi

2022/12/18
 *)

(**
# はじめに

Prologは、第1階述語論理の構文的なサブセットである「ホーン節」Horn Clauseの自動証明を
動作原理とするプログラミング言語です。
ここで使われる自動証明のことを「導出原理」Resolution Principleと呼びます。

ここでは、Prologのプログラムを論理式として証明してみましょう。

手で証明するのも大変なので、定理証明系（Coq/MathComp）を使ってみます。
すると、Prologと論理学や、Coqとの関係が見えてくるとおもいます。

この記事のプログラムは以下にありますが、実行にはCoq/MathCompは必要です。




まず、対象とする論理式を明確にしてみます。
 *)

(**
# Prologのプログラムとしての論理式

ホーン節ということで間違いないのですが、後述する理由で、
「ホーン節」と「ゴール節」のふたつに分けて説明します。
いずれも定義は見たままのものなので、説明は省略します。
ここで、$ k,l,m,n \ge 0 $ とします。

- ホーン節

P、Qは原始論理式（∧、∨、〜、∀、∃などの論理記号を含まない論理式）
で、False（⊥）でないものとします。
論理記号の使い方の次のような文法的な制限を加えた論理式をホーン節といいます。

```math
\forall x_{1}~\forall x_{2}~ …\forall x_{n}~[(P_{1}~\land~P_{2}~\land~…~\land~P_{m})~\to~Q]
```

```coq
forall x1 x2 ... xn, P1 P2 ... Pm -> Q.
```

Prologのプログラムでは、次のように表します。

```Prolog
Q :- P1, P2, ... Pm.
```

量化子の変数は大文字で書き、``∀x``は書きません。
また、``:- true``は省略しす。


- ゴール節

Rは原始論理式で、False（⊥）でないものとします。
次の文法的な制限を加えた論理式をゴール節といいます。

```math
\exists x_{1}~\exists x_{2}~ …\exists x_{l}~[R]
```

```coq
exists x1 x2 ... xl, R.
```

Prologのプログラムでは、次のように表します。

```Prolog
?-R.
```

量化子の変数は大文字で書き、``∃x``は書きません。

- Prologのプログラムの論理式

複数のホーン節 $ H_{i} $ とひとつのゴール節 $ G $ からなります。

```math
H_{1}~\land~H_{2}~\land~…\land~H_{k}~\to~G
```

Prologのプログラムは、ホーン節を並べたものです。
並べ方の順番は自動証明（導出原理）における選択の順番に反映されます。
ゴール節は対話形式で入力したり
コマンドラインの引数で与える場合が多いので``?-``はあまり使わないかもしれません。

この後、Prologで定数やデータ構造扱うためには、スコーレム関数(Skolem function)の説明が
必要ですが、多少本題からずれるので、省略させてください。
ここでは、PrologもCoqも同様の定数や、リストのようなデータ構造が使えることを前提とします。
*)

(**
# Prologのプログラムの例

例によって、リストの反転を考えてみます。

```
rev(L, RL) :-
    rev3(L, [],  RL).
rev3([X|XS], ACC, RL) :-
     rev3(XS, [X|ACC], RL).
rev3([], RL, RL).
```

これに対して、ふたつのゴール、ゴール1

```
?- rev([1, 2, 3], RL).
```

と、ゴール2について

```
?- rev(L, [3, 2, 1]).
```

実行してみます。


なお、λPrologの文法だと次のようになります。
この場合は、述語の引数のして方法が違うだけですね。
```
pred rev i:list A, o:list A.
rev L RL :-
    rev3 L [] RL.
rev3 [X|XS] ACC RL :-
     rev3 XS [X|ACC] RL.
rev3 [] RL RL.
```

ホーン節の部分を論理式で表すと

```math

\forall L~\forall RL~[rev3(L, [], RL)~\to~rev(L, RL)]
\\\land\\
\forall X~\forall XS~\forall ACC~\forall RL~[rev3(XS, [X|ACC], RL~\to~rev3([X|XS],ACC,RL)]
\\\land\\
\forall RL~[true~\to~rev3([], RL, RL)]
```

ゴール1は

```math
\exists RL~[rev([1,2,3], RL)]
```

ゴール2は

```math
\exists L~[rev(L, [3,2,1])]
```

*)
From mathcomp Require Import all_ssreflect.

Variable rev : list nat -> list nat -> Prop.
Variable rev3 : list nat -> list nat -> list nat -> Prop.

(**
ホーン節の部分は以下のようになります。
ここでは便宜的にDefinitionでまとめていますが、論理式としての意味は変わりません。
*)
Definition prog0 :=
  (forall L RL, rev3 L [::] RL -> rev L RL)
  /\
    (forall X XS ACC RL, rev3 XS (X :: ACC) RL -> rev3 (X :: XS) ACC RL)
  /\
    (forall RL, rev3 [::] RL RL).
      
(**
ゴールの部分は
*)
Definition goal1 := exists RL, rev [:: 1; 2; 3] RL.
Definition goal2 := exists L, rev L [:: 9; 8; 7].

(**
Coqで証明してみます。Coqは``∃``を自動で証明できないので、
答えを教えてあげる必要があります。
しかし、Coqにの導出原理に基づく自動証明のタクティク``auto``があるので
それを使ってみます。
*)
Goal prog0 -> goal1.
Proof.
  rewrite /prog0 /goal1.
  case=> [H [Hcons Hnil]].
  exists [:: 3; 2; 1].
  apply: (H).
  apply: (Hcons).
  apply: (Hcons).
  apply: (Hcons).
  apply: (Hnil).
  
  Restart.
  case=> [H [Hcons Hnil]].
  exists [:: 3; 2; 1].
  debug auto.
Qed.

Goal prog0 -> goal2.
Proof.
  rewrite /prog0 /goal2.
  case=> [H [Hcons Hnil]].
  exists [:: 7; 8; 9].
  debug auto.
Qed.

(**
以上から、Prologのプログラムは、Coqの``auto``タクティクで証明できる（場合もある）ことが
わかりました。
*)

(**
# 補足説明

## 古典論理と直観主義論理

まず、ゴール節の否定を考えます。$ (\lnot~R) \Leftrightarrow (R~\to~False) $
なので、ホーン節の``→``の右をFalseにしたものになります。

```math
\lnot(\exists x_{1}~\exists x_{2}~ …\exists x_{l}~[R])
\\
\forall x_{1}~\forall x_{2}~ …\forall x_{l}~[\lnot~R]
\\
\forall x_{1}~\forall x_{2}~ …\forall x_{l}~[R~\to~False]
```

Prologのプログラムの論理式を否定します。さらに、含意を論理和と否定のかたち
$ (H~\to~G) \Leftrightarrow (\lnot~H~\lor~G) $ にします。
すると、ホーン節とゴール節の否定を連言になります。
上でみたように、ゴール節の否定は（特別な）ホーン節ですから、
Prologのプログラムは、ホーン節の連言ということができます。

```math
\lnot~(H_{1}~\land~H_{2}~\land~…\land~H_{k}~\to~G)
\\
\lnot~(\lnot~(H_{1}~\land~H_{2}~\land~…\land~H_{k})~\lor~G)
\\
\lnot(\lnot H_{1}~\lor~\lnot H_{2}~\lor~…\lor~\lnot H_{k}~\lor~G)
\\
H_{1}~\land~H_{2}~\land~…\land~H_{k}~\land~\lnot~G
```

最初にPrologのプログラムの論理式を否定を考えたのは、
導出原理は、論理式の反駁（はんばく）を導くことだからです。

しかし、お気づきのとおり、上記の論理式を導くには
古典論理が必要になります。
これに対して、ホーン節とゴール節を別々に定義することで、
Prologの論理式の意味を直観主義論理の範囲で示すことができ、
同じく、直観主義論理を使用するCoqの上で証明することができるわけです。


## Prologの不完全性

実は、Prologでgoal2に対して実行すると無限ループになります。
なぜなら、``rev RL [9,8,7]``に対して、rev3のはじめの節が選ばれるために、
(``rev3 [X|XS] ACC R :- rev3 XS [X|ACC] R.``)に対して、
``rev3 RL [] [9,8,7]``が実行されますが、
rev3の第3引数は再帰呼び出しに対して、リストの分解が行われないため、
再帰呼び出しの終了判定がなく、無限ループになってしまいます。

これは、証明できるべき命題が証明できないという意味で、定理証明系としての
Prologの「不完全性」の一例になっています。

これに対して、Coqは、existsに対して手で値を設定しなければならない代わりに、
このような問題が生じません。その意味ではCoqは「完全」なわけです。


## cut述語について

Prologにはcut述語、別名、カットオペレータ(``!``)があります。
これは、Prologの自動証明において、
ホーン節のしらみつぶしの選択を木構造の検索と見立てた場合、
バックトラックが生じた際に、ツリーの検索の一部をカット(枝を刈る)して、
検索せずにただちに失敗(fail)とする、ということからこの名前があります。

cut述語は、論理式としてもProlog言語ではなく、手続言語の側面を実現するものなので、
本資料では触れませんでした。

Coqにもcutタクティクがありますが、証明論におけるカット除去定理
（``A -> C`` かつ ``C -> B``なら``C``を除去して``A -> B``を導ける）
の逆のことを行うもので、Coqのゴール``A -> B`` を ``C -> B`` に置き換えることをします。
もちろん、そのあとに、``A -> C``を証明させられることになります。

このふたつは全く別の概念なので、注意してください。

 *)

(* END *)
