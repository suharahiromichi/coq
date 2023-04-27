(**
Coq-Elpi によるタクティクの作成（その1の2）
=====================

@suharahiromichi

2022/12/31

2023/1/28 ProofCafe
*)

(**
定理証明系Coqには、Embeddable Lambda Prolog Interpreter (ELPI [1]) によってタクティク（証明戦略）を
作成するためのパッケージ ``Coq-Elpi``が用意されています([3]から[6])。

``Coq-Elpi``を使う最初のサンプルとして、``P -> Q -> (P /\ Q)``を証明するタクティクを作成してみます。

この記事のソースコードは Coq のソースファイルであり、以下にあります。

https://github.com/suharahiromichi/coq/tree/master/elpi/coq_elpi_tactic_sample_1_2.v

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

(**
また、refine で与える項には未定部分（注2）があってもよく、
Holeの部分が次の（サブ）ゴールになります。

（注2） Holeと呼び、``_``で表します。
*)
Lemma test : forall (P Q : Prop), P -> Q -> (P /\ Q).
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

が与えられます。通常、

```
solve (goal Ctx Trigger Type Proof Args as G) GL :- なんとか
```

ここで、

- G はElpiとして、入力です。Gは、``as``によって、``goal Ctx Trigger Type Proof Args`` と等しくなります。
``as`` は、Coqの``match``の``as``と似ていますが、Elpi上の``=``の意味になります。

- GL はElpiとして出力です。残った(サブ)ゴールを返します。一般にサブゴールは複数ですから、リストになっています。
通常は、直接扱うことはなく、後述する``refine``から返します。
ゴールに対して処理をしない（次の``show``のような場合）は、``_``としておけばよいです。

- Ctxは、コンテキストの内容のリストで、リストの要素は次のどちらかになります。
  - ``decl <項1> <Coq表示名> <項2>`` このとき、項2は項1の型
  - ``def <項1> <Coq表示名> <項2> <項3>`` このとき、項2は項1の型、項3は定義

  ``def`` は、Coqのsetタクティクを使った場合なので、この記事では使いません。

- Triggerは、制約論理のサスペンドした条件であり、これに値を代入することで、証明が進みます。
前述の通り、そこにHoleがあった場合、そこが次の（サブ）ゴールになります。

- Typeは、ゴールの命題（カリー・ハワード対応の型）です。

- Proofは、ゴールの証明（カリー・ハワード対応の値）です。通常は参照することも代入することもありません。
ここに直接代入すると、「No more subgoals」になるのに、Qedでエラーになるという「不健全」な
ことができます([6])。おまけ参照。

- Argsは、Elpiで定義したタクティクに与えられた引数のリストです。
この記事では、タクティクに引数を与えないので、使いません。``[]``になっています。

このように、Triggerに値を代入する（Elpiのレベルで``=``を使ってユニフィケーションする）ことで
証明が進むことに間違いはないのですが、通常Elpiの組込述語である``refine``述語を使います。

書式を端折って書くと、次にようになります。

```
solve (goal Ctx Trigger Type Proof Args as G) GL :-
  refine <Triggerに代入したい項> G GL.
```

第2引数と第3引数には、solveの第1引数のGと第2引数のGLを渡します。
``refine``の結果として、GLにサブゴールのリストが返されるので、それをそのまま``solve``に返します。
あとは、Coqの証明エンジンがサブゴールの処理をしてくれます。
*)

(**
### elpi id なにもしないタクティク

なにもしないのであれば、``solve``の引数になにもなくてよいので、
以下のようになります。
*)
Elpi Tactic id.
Elpi Accumulate lp:{{
  solve _ _ :-
    true.         % true は省略してよい。
}}.
Elpi Typecheck.

Goal True.
Proof.
  elpi id.
  exact I.
Qed.

(**
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


(注3) 正確には、Hereditary Harrop Formula [1] というべき。

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
## Coq-Elpi のタクティクの例

補題testをみるとrefineは3箇所、2種類使われています。
ひとつは``refine (conj _ _)``であり、
もうひとつは``refine HP``と``refine HQ``です。
この2種類に分けて説明します。


### elpi split

前者については、ゴールのTypeが``_ /\ _`` のときに、
Triggerに``conj _ _``を代入すればよいのですが、
これらはCoqの項であるので、``{{}}``で囲む必要があります。

すると、以下のようになります。Coqのsplitタクティクと同じなので、splitと名付けます。
*)
Elpi Tactic split.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger {{ _ /\ _ }} Proof Args as G) GL :-
    refine {{ conj _ _ }} G GL.
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
    refine H G GL.
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

(**
# おまけ elpi admit (不健全なタクティク)
*)
Elpi Tactic admit.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger Type Proof Args as G) GL :-
    Proof = {{I}}.
}}.

Goal False.
Proof.
  elpi admit.
Fail Qed.     (* Qed で失敗する。 *)
Admitted.

(* END *)
