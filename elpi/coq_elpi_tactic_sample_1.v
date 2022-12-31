(**
Coq-Elpi によるタクティクの作成（その1）
=====================

@suharahiromichi

2022/12/31
*)

(**
定理証明系Coqには、Embeddable Lambda Prolog Interpreter (ELPI [1]) によってタクティク（証明戦略）を
作成するためのパッケージ ``Coq-Elpi``が用意されています([3]から[6])。

``Coq-Elpi``を使う最初のサンプルとして、``P -> Q -> (P /\ Q)``を証明するタクティクを作成してみます。

この記事のソースコードは Coq のソースファイルであり、以下にあります。

https://github.com/suharahiromichi/coq/tree/master/elpi/coq_elpi_tactic_sample_1.v

最初に明かすと、これは文献[6]の勉強ノートにすぎません。
正確な記述を要求される方は、参考文献[3]から[6]を参照してください。
*)

(**
# Coqによる証明の復習

最初に、Coqによる証明がどのようなものか、復習してみましょう。
例は、一貫して``P -> Q -> (P /\ Q)``を使います。

Coqによる証明は、通常は、コンテキストにある仮説（注1）をゴールに適用（apply）することに
よっておこなれますが、もう少し下位のレベルで考えると、
ゴールの型（命題）に対する項（証明）をrefine ([2])で与えていくことになります。
カリー・ハワード対応ですね。

（注1） 通常 hypothesis の頭文字``H``を先頭に付けて呼ぶことが多いです。
*)
Lemma test1 : forall (P Q : Prop), P -> Q -> (P /\ Q).
Proof.
  intros P Q HP HQ.
(**
```
P : Prop
Q : Prop
HP : P
HQ : Q
============
Goal : P /\ Q
```
*)
  refine (conj HP HQ).
Qed.

(**
また、refine で与える項には未定部分（注2）があってもよく、
Holeの部分が次の（サブ）ゴールになります。

（注2） Holeと呼び、``_``で表します。
*)
Lemma test2 : forall (P Q : Prop), P -> Q -> (P /\ Q).
Proof.
  intros P Q HP HQ.
(* Goal : P /\ Q *)
  refine (conj _ _).
(* Goal : P *)
  refine HP.
(* Goal : Q *)
  refine HQ.
Qed.

(**
# Coq-Elpi による作成例

## 全般の説明

最初に、Coq の elpiライブラリをインポートします。
*)
From elpi Require Import elpi.

(**
Elpiで定義したタクティクは、Elpiの述語``solve G GL``の形式で呼び出されます。

Gには、Elpiのコンストラクタ``goal``で構成されたデータ構造

```
goal Ctx Trigger Type Proof Args
```

が与えられます。ここで、

- Ctxは、コンテキストの内容のリストで、リストの要素は次のどちらかになります。
  - ``decl <項1> <Coq表示名> <項2>`` このとき、項2は項1の型
  - ``def <項1> <Coq表示名> <項2> <項3>`` このとき、項2は項1の型、項3は定義

  ``def`` は、Coqのsetタクティクを使った場合なので、この記事では使いません。

-  Triggerは、制約論理のサスペンドした条件であり、これに値を代入することで、証明が進みます。
前述の通り、そこにHoleがあった場合、そこが次の（サブ）ゴールになります。

- Typeは、ゴールの命題（カリー・ハワード対応の型）です。

- Proofは、ゴールの証明（カリー・ハワード対応の値）です。通常は参照することも代入することもありません。
ここに直接代入すると、「No more subgoals」になるのに、Qedでエラーになるという「不健全」な
ことができるのだそうです([6])。

- Argsは、Elpiで定義したタクティクに与えられた引数のリストです。
この記事では、タクティクに引数を与えないので、使いません。``[]``になっています。


GLについては説明を省きます。

### elpi show

Elpiで書いたタクティクの例として、Ctx、Proof、Typeを表示するだけのタクティクshowを示します。
``elpi show``で呼び出すことができます([6])。

CoqのコマンドにElpiが追加されるので、これを次の例のように使います。

そして、Elpiのコードは``lp:{{}}``で囲んで埋め込みます。
さらにそのなかに``{{}}``で囲んでCoqの項を書くことができます。
さらにそのなかに``lp:{{}}``で囲んで…とネストできます。
また、``lp:{{A}}``のように``lp:{{}}``の中身が変数などの場合は、``lp:A``と略すことができます。


このように、1つのElpiの節（注3）のなかに、Elpiの項とCoqの項を混ぜて書くことができますが、
Elpiの変数は、1つのElpiの節(Clause)をスコープとすることに違いはありません。


(注3) 正確には、Hereditary Harrop Formula [1]　というべき。
*)
Elpi Tactic show.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger Type Proof Args) _ :-
    coq.say "Goal:" Ctx "|-" Proof ":" Type.
}}.
Elpi Typecheck.
(**
ここでの表示は、Coq-Elpi内部のHOAS表現([4])であり、Coqでの表現と大きく異なります。
そのため、参考程度にしてください。
*)

(**
前節では、test1のまとめてイッキに証明する場合と、test2のHoleを使い
サブゴールにわけて証明する場合を示しました。
そのどちらも重要であるため、ここでもその2通りの方法で説明します。

解り易さから、test2に対応するHole-サブゴールの例から説明します。
*)

(**
## Hole-サブゴールで証明する例

test2に対応する例から考えます、test2をみるとrefineは3箇所、2種類使われています。
ひとつは``refine (conj _ _)``であり、
もうひとつは``refine HP``と``refine HQ``です。

### elpi split

前者については、ゴールのTypeが``_ /\ _`` のときに、
Triggerに``conj _ _``を代入すればよいのですが、
これらはCoqの項であるので、``{{}}``で囲む必要があります。

すると、以下のようになります。Coqのsplitタクティクと同じなので、splitと名付けます。
*)
Elpi Tactic split.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger {{ _ /\ _ }} Proof Args as G) GL :-
    Trigger = {{ conj _ _ }}.
  solve _ _ :-
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

(**
### elpi assumption

後者(例えば``refine HP``)の場合は、ゴール``P``に対して、コンテキストのリストから
型``P``をもつ仮説``HP``を探し出して、それをrefineする必要があります。

コンテキストから探し出すには、組込述語 stdlib ([7])のstd.memを使います。

ゴールの型はsolveの呼び出しの``goal Ctx Trigger Type Proof Args``
のTypeですから、Ctxの中から``decl H _ Type``である``H``を探すことになります。

declの2番目の``_``は、Coq表示名ですが、これを手がかりにすることはしないので、
無視するようにします。ゴールのHoleとは関係ありません。

実はCoqのassumptionタクティクと同じ動きなので、assumptionと名付けます。
*)
Elpi Tactic assumption.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger Type Proof Args as G) GL :-
    std.mem Ctx (decl H _ Type), coq.say "decl" H ":" Type,
	  Trigger = H.
  solve _ _ :-
    coq.ltac.fail _ "no such hypothesis".
}}.
Elpi Typecheck.

(**
### 実行例

実行例を以下に示します。Qedが成功しているので、うまくできたようです。
*)
Lemma test21 : forall (P Q : Prop), P -> Q -> (P /\ Q).
Proof.
  intros P Q HP HQ.
(* Goal : P /\ Q *)
  elpi split.
(* Goal : P *)  
  elpi assumption.
(* Goal : Q *)
  elpi assumption.
Qed.

(**
## イッキに証明する例

### pf_conj

test1に対応する例を考えます。

この場合は、ゴール ``A /\ B``のAとBのそれぞれについて、
コンテキストからそれを型とする項を探す必要があります。
また、探しだした結果HAやHBを``conj HA HB``として、Triggerに渡す必要があります。

A、B、HAとHBは、Coqの項の中のElpiの変数であるので、
Coqの項``{{}}``の中に、``lp:A``や``lp:B``のように書く必要があります。
*)

Elpi Tactic pf_conj.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger {{ lp:A /\ lp:B }} Proof Aargs as G) GL :-
    std.mem Ctx (decl HA _ A), coq.say "decl" HA ":" A,
    std.mem Ctx (decl HB _ B), coq.say "decl" HB ":" B,
    Trigger = {{ conj lp:HA lp:HB }}.
  solve _ _ :-
    coq.ltac.fail _ "cannot pf_conj".
}}.
Elpi Typecheck.

(**
### 実行例

実行例を以下に示します。Qedが成功しているので、これもうまくできたようです。
*)
Lemma test12 : forall (P Q : Prop), P -> Q -> (P /\ Q).
Proof.
 intros P Q HP HQ.
 elpi pf_conj.
Qed.

(**
# 参考文献

[1] "λProlog (Lambda Prolog) の紹介"

<https://qiita.com/suharahiromichi/items/a046859da0c0883e7304>


[2] "Coq Docs - Basic proof writing - Tactics - refine"

<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.refine>


[3] "Tutorial on the Elpi programming language"

<https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html>


[4] "Tutorial on the HOAS for Coq terms"

<https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_HOAS.html>


[5] "Tutorial on Coq commands"

<https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_command.html>


[6] "Tutorial on Coq tactics"

<https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_tactic.html>


[7] ELPI の組込述語 (stdlib編)

<https://qiita.com/suharahiromichi/items/1d200a9320e04ca21953>
*)

(* END *)
